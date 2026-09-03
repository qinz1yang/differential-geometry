import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.Coefficient.L2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.LieHigherOrderCoefficientField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.MetricComparisonEndomorphismJetBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.CovariantOrderFibreNormBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.RaisedKoszul.JetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.RecoveryEndomorphismJetBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.JetTower
import DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Identities
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Algebra
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SymmAbsorbedCoeffInputReindexBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.LoweredCoefficient
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.FirstOrderTerm.ConnectionDifferenceBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.FirstOrderTerm.BackgroundCoefficientBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.FirstOrderTerm.PointwiseIdentity
import DifferentialGeometry.Analysis.Estimates.ProductBounds
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature

noncomputable section


open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open DifferentialGeometry.TensorMultilinear
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (metricPerturbationPath convexPerturbation
  convexPerturbation_gFibreOpBound metricPerturbationPath_inner_of_mem Icc_subset_metricPerturbationPathDomain)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (g0FlatCLM metricComparisonEndomorphism
  metricComparisonEndomorphism_apply metricComparisonEndomorphism_eq_diff_add_id metricComparisonDifferenceEndomorphism
  cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

abbrev lieFirstOrderPiece := @deTurckLieTraceCoeffPiece

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem deTurckLieFirstOrderCoeff_eq_lieFirstOrderPiece_sum (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieFirstOrderCoeff (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaC lieFirstOrderRhoSlot0
          (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)
        + (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaA (Equiv.refl (Fin 3))
            (connectionDifferenceSection (I := I) g₁ g₀)
          + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaA (Equiv.refl (Fin 3))
            (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg)
          - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaC (Equiv.refl (Fin 3))
            (connectionDifferenceSection (I := I) g₁ g₀)
          - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaD lieFirstOrderRhoSlot0
            (connectionDifferenceSection (I := I) g₁ g₀)
          - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieFirstOrderRhoSlot1
            (connectionDifferenceSection (I := I) g₁ g₀)
          - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaF (Equiv.refl (Fin 3))
            (connectionDifferenceSection (I := I) g₁ g₀))
        + (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaASwap (Equiv.refl (Fin 3))
            (connectionDifferenceSection (I := I) g₁ g₀)
          + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaASwap (Equiv.refl (Fin 3))
            (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg)
          - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaCSwap (Equiv.refl (Fin 3))
            (connectionDifferenceSection (I := I) g₁ g₀)
          - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaDSwap lieFirstOrderRhoSlot0
            (connectionDifferenceSection (I := I) g₁ g₀)
          - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaESwap lieFirstOrderRhoSlot1
            (connectionDifferenceSection (I := I) g₁ g₀)
          - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaFSwap (Equiv.refl (Fin 3))
            (connectionDifferenceSection (I := I) g₁ g₀))
        + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieFirstOrderRhoSlot0
            (connectionDifferenceSection (I := I) g₁ g₀) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hCLM : ∀ D : Tensor0SSpace 3 I x,
      (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieFirstOrderCoeff (I := I) (M := M) g₀ g₁ g_bg).toSection x) D =
      (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaC lieFirstOrderRhoSlot0
            (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)
          + (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaA (Equiv.refl (Fin 3))
              (connectionDifferenceSection (I := I) g₁ g₀)
            + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaA (Equiv.refl (Fin 3))
              (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaC (Equiv.refl (Fin 3))
              (connectionDifferenceSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaD lieFirstOrderRhoSlot0
              (connectionDifferenceSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieFirstOrderRhoSlot1
              (connectionDifferenceSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaF (Equiv.refl (Fin 3))
              (connectionDifferenceSection (I := I) g₁ g₀))
          + (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaASwap
            (Equiv.refl (Fin 3))
              (connectionDifferenceSection (I := I) g₁ g₀)
            + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaASwap
              (Equiv.refl (Fin 3))
              (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaCSwap
              (Equiv.refl (Fin 3))
              (connectionDifferenceSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaDSwap lieFirstOrderRhoSlot0
              (connectionDifferenceSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaESwap lieFirstOrderRhoSlot1
              (connectionDifferenceSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaFSwap
              (Equiv.refl (Fin 3))
              (connectionDifferenceSection (I := I) g₁ g₀))
          + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieFirstOrderRhoSlot0
              (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) D := by
    intro D
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective (𝕜 := ℝ) (I := I) (s := 2) (x := x)
    change Tensor0SSpace.toModel _ = Tensor0SSpace.toModel _
    apply ContinuousMultilinearMap.ext
    intro w
    exact lieFirstOrder_coeff_pieces_pointwise (I := I) (M := M) g₀ g₁ g_bg x D
      (fun j : Fin 2 => ((w j : E) : TangentSpace I x))
  exact ContinuousLinearMap.ext hCLM

theorem lieFirstOrderPiece_connectionDifference_metricPerturbationPath_jetL2_perOrder_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (connectionDifferenceSection (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g₀))‖ ^ 2 ≤
            P i := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_metricPerturbationPath_riemannianFiberNormSq_ballUniform (I := I) (M := M) g₀ a (R := R) hδ₀
    obtain ⟨Q, hQ_nn, hQ⟩ :=
      traceHessianCoeff_metricPerturbationPath_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
      lieFirstOrder_connectionDifference_bounds (I := I) (M := M) g₀ a ha_super hR hδ₀
    obtain ⟨C2, hC2_nn, hC2⟩ := lieFirstOrder_twoTerm_top_fn (I := I) (M := M) g₀ a
    refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
        (C2 i * (((Module.finrank ℝ E : ℝ) ^ 2 * Λcd) * (∑ n ∈ Finset.range (i + 1), Q n)
          + Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * Fcd i))), ?_, ?_⟩
    · intro i
      refine mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i)
        (mul_nonneg (hC2_nn i) (add_nonneg ?_ ?_))
      · exact mul_nonneg (mul_nonneg (by positivity) hΛcd_nn)
          (Finset.sum_nonneg fun n _ => hQ_nn n)
      · exact mul_nonneg hΛcom_nn (mul_nonneg (by positivity) (hFcd_nn i))
    · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
      have := hM
      obtain ⟨htie, hδP, hδP_le⟩ :=
        lieFirstOrder_metricPerturbationPath_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
      have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
        lieFirstOrder_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
      have hPball := lieFirstOrder_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
        hTball hT'ball hs
      obtain ⟨hcd0, hcdL2⟩ := hcd (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
        (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤
          (Real.sqrt Λcom) ^ 2 := by
        intro x
        rw [Real.sq_sqrt hΛcom_nn, lieFirstOrder_riemannianFiberNormSq_dLTC_toSection_eq]
        exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
      have hFS : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (deTurckLieTraceCoeff (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 ≤
          ∑ n ∈ Finset.range (i + 1), Q n := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn_le : n ≤ a := by have := Finset.mem_range.mp hn; omega
        rw [lieFirstOrder_normSq_iteratedCovGrad_dLTC_eq]
        exact hQ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball n hn_le s hs
      have hT0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
            (connectionDifferenceSection (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
              g₀))).toSection x) ≤
          (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λcd)) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (mul_nonneg (by positivity) hΛcd_nn)]
        refine le_trans (lieFirstOrder_riemannianFiberNormSq_sE2_zero_le (I := I) (M := M) g₀ _ x) ?_
        exact mul_le_mul_of_nonneg_left (hcd0 x) (by positivity)
      have hFT : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
              (connectionDifferenceSection (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g₀)))‖ ^ 2 ≤
          (Module.finrank ℝ E : ℝ) ^ 2 * Fcd i := by
        refine le_trans (Finset.sum_le_sum fun l _ =>
          lieFirstOrder_normSq_iteratedCovGrad_sE2_le (I := I) (M := M) g₀ _ l) ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hcdL2 i hi) (by positivity)
      have hmaster := lieFirstOrder_piece_normSq_le (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ' ρ
        (connectionDifferenceSection (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g₀) i
        (C2 i) (Real.sqrt Λcom) (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λcd))
        (∑ n ∈ Finset.range (i + 1), Q n) ((Module.finrank ℝ E : ℝ) ^ 2 * Fcd i)
        (hC2_nn i) hFS hFT
        (hC2 i hi _ _ (Real.sqrt Λcom) (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λcd))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hS0 hT0)
      refine le_trans hmaster (le_of_eq ?_)
      rw [Real.sq_sqrt hΛcom_nn, Real.sq_sqrt (mul_nonneg (by positivity) hΛcd_nn)]
  · have hIsE := not_nonempty_iff.mp hM
    refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
    have h0 := lieFirstOrder_norm_isEmpty (I := I) (M := M) hIsE g₀ 3 (2 + i)
      (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ' ρ
          (connectionDifferenceSection (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g₀)))
    rw [h0]
    norm_num

theorem lieFirstOrderPiece_connectionDifferenceBackground_metricPerturbationPath_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀
                  (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg))‖ ^ 2 ≤ P i := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_metricPerturbationPath_riemannianFiberNormSq_ballUniform (I := I) (M := M) g₀ a (R := R) hδ₀
    obtain ⟨Q, hQ_nn, hQ⟩ :=
      traceHessianCoeff_metricPerturbationPath_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
      lieFirstOrder_connectionDifference_bounds (I := I) (M := M) g₀ a ha_super hR hδ₀
    obtain ⟨Λfx, hΛfx_nn, hΛfx⟩ :=
      exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 2
        (lieFirstOrderFixCd (I := I) (M := M) g₀ g_bg)
    obtain ⟨C2, hC2_nn, hC2⟩ := lieFirstOrder_twoTerm_top_fn (I := I) (M := M) g₀ a
    refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
        (C2 i * (((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx)) *
            (∑ n ∈ Finset.range (i + 1), Q n)
          + Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Fcd i +
              2 * ∑ l ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 1 2 l
                  (lieFirstOrderFixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2)))), ?_, ?_⟩
    · intro i
      refine mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i)
        (mul_nonneg (hC2_nn i) (add_nonneg ?_ ?_))
      · refine mul_nonneg (mul_nonneg (by positivity) (by linarith))
          (Finset.sum_nonneg fun n _ => hQ_nn n)
      · refine mul_nonneg hΛcom_nn (mul_nonneg (by positivity) ?_)
        have h1 : (0 : ℝ) ≤ Fcd i := hFcd_nn i
        have h2 : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieFirstOrderFixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2 :=
          Finset.sum_nonneg fun l _ => sq_nonneg _
        linarith
    · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
      have := hM
      obtain ⟨htie, hδP, hδP_le⟩ :=
        lieFirstOrder_metricPerturbationPath_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
      have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
        lieFirstOrder_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
      have hPball := lieFirstOrder_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
        hTball hT'ball hs
      obtain ⟨hcd0, hcdL2⟩ := hcd (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
        (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
      have hΨ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤
          2 * Λcd + 2 * Λfx := by
        intro x
        rw [lieFirstOrder_connectionDifferenceBackground_decomp (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg]
        refine le_trans (lieFirstOrder_riemannianFiberNormSq_toSection_add_le (I := I) (M := M) g₀ 1 2 _ _ x) ?_
        have h1 := hcd0 x
        have h2 := hΛfx x
        linarith
      have hΨL2 : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 2 l
            (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
          2 * Fcd i + 2 * ∑ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieFirstOrderFixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2 := by
        have hstep : ∀ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                (connectionDifferenceSection (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g₀)‖ ^ 2 +
              2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                (lieFirstOrderFixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2 := by
          intro l _
          rw [lieFirstOrder_connectionDifferenceBackground_decomp (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg]
          exact lieFirstOrder_normSq_iteratedCovGrad_add_le (I := I) (M := M) g₀ 1 2 l _ _
        refine le_trans (Finset.sum_le_sum hstep) ?_
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have h1 := mul_le_mul_of_nonneg_left (hcdL2 i hi) (by norm_num : (0:ℝ) ≤ 2)
        linarith
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤
          (Real.sqrt Λcom) ^ 2 := by
        intro x
        rw [Real.sq_sqrt hΛcom_nn, lieFirstOrder_riemannianFiberNormSq_dLTC_toSection_eq]
        exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
      have hFS : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (deTurckLieTraceCoeff (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 ≤
          ∑ n ∈ Finset.range (i + 1), Q n := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn_le : n ≤ a := by have := Finset.mem_range.mp hn; omega
        rw [lieFirstOrder_normSq_iteratedCovGrad_dLTC_eq]
        exact hQ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball n hn_le s hs
      have hΨ0_nn : (0 : ℝ) ≤ 2 * Λcd + 2 * Λfx := by linarith
      have hT0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
            (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg))).toSection x) ≤
          (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx))) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (mul_nonneg (by positivity) hΨ0_nn)]
        refine le_trans (lieFirstOrder_riemannianFiberNormSq_sE2_zero_le (I := I) (M := M) g₀ _ x) ?_
        exact mul_le_mul_of_nonneg_left (hΨ0 x) (by positivity)
      have hFT : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
              (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)))‖ ^ 2 ≤
          (Module.finrank ℝ E : ℝ) ^ 2 * (2 * Fcd i + 2 * ∑ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieFirstOrderFixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2) := by
        refine le_trans (Finset.sum_le_sum fun l _ =>
          lieFirstOrder_normSq_iteratedCovGrad_sE2_le (I := I) (M := M) g₀ _ l) ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hΨL2 (by positivity)
      have hmaster := lieFirstOrder_piece_normSq_le (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ' ρ
        (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg) i
        (C2 i) (Real.sqrt Λcom)
        (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx)))
        (∑ n ∈ Finset.range (i + 1), Q n)
        ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Fcd i + 2 * ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 2 l
            (lieFirstOrderFixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2))
        (hC2_nn i) hFS hFT
        (hC2 i hi _ _ (Real.sqrt Λcom)
          (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx)))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hS0 hT0)
      refine le_trans hmaster (le_of_eq ?_)
      rw [Real.sq_sqrt hΛcom_nn, Real.sq_sqrt (mul_nonneg (by positivity) hΨ0_nn)]
  · have hIsE := not_nonempty_iff.mp hM
    refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
    have h0 := lieFirstOrder_norm_isEmpty (I := I) (M := M) hIsE g₀ 3 (2 + i)
      (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ' ρ
          (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)))
    rw [h0]
    norm_num

theorem lieFirstOrderPiece_psiB_metricPerturbationPath_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀
                  (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg))‖ ^ 2 ≤ P i := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_metricPerturbationPath_riemannianFiberNormSq_ballUniform (I := I) (M := M) g₀ a (R := R) hδ₀
    obtain ⟨Q, hQ_nn, hQ⟩ :=
      traceHessianCoeff_metricPerturbationPath_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Λpb, Fpb, hΛpb_nn, hFpb_nn, hpb⟩ :=
      lieFirstOrder_backgroundCoefficient_bounds (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
    obtain ⟨C2, hC2_nn, hC2⟩ := lieFirstOrder_twoTerm_top_fn (I := I) (M := M) g₀ a
    refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
        (C2 i * (((Module.finrank ℝ E : ℝ) ^ 2 * Λpb) * (∑ n ∈ Finset.range (i + 1), Q n)
          + Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * Fpb i))), ?_, ?_⟩
    · intro i
      refine mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i)
        (mul_nonneg (hC2_nn i) (add_nonneg ?_ ?_))
      · exact mul_nonneg (mul_nonneg (by positivity) hΛpb_nn)
          (Finset.sum_nonneg fun n _ => hQ_nn n)
      · exact mul_nonneg hΛcom_nn (mul_nonneg (by positivity) (hFpb_nn i))
    · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
      have := hM
      obtain ⟨htie, hδP, hδP_le⟩ :=
        lieFirstOrder_metricPerturbationPath_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
      have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
        lieFirstOrder_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
      have hPball := lieFirstOrder_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
        hTball hT'ball hs
      obtain ⟨hpb0, hpbL2⟩ := hpb (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
        (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤
          (Real.sqrt Λcom) ^ 2 := by
        intro x
        rw [Real.sq_sqrt hΛcom_nn, lieFirstOrder_riemannianFiberNormSq_dLTC_toSection_eq]
        exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
      have hFS : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (deTurckLieTraceCoeff (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 ≤
          ∑ n ∈ Finset.range (i + 1), Q n := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn_le : n ≤ a := by have := Finset.mem_range.mp hn; omega
        rw [lieFirstOrder_normSq_iteratedCovGrad_dLTC_eq]
        exact hQ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball n hn_le s hs
      have hT0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
            (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg))).toSection x) ≤
          (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λpb)) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (mul_nonneg (by positivity) hΛpb_nn)]
        refine le_trans (lieFirstOrder_riemannianFiberNormSq_sE2_zero_le (I := I) (M := M) g₀ _ x) ?_
        exact mul_le_mul_of_nonneg_left (hpb0 x) (by positivity)
      have hFT : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
              (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)))‖ ^ 2 ≤
          (Module.finrank ℝ E : ℝ) ^ 2 * Fpb i := by
        refine le_trans (Finset.sum_le_sum fun l _ =>
          lieFirstOrder_normSq_iteratedCovGrad_sE2_le (I := I) (M := M) g₀ _ l) ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hpbL2 i hi) (by positivity)
      have hmaster := lieFirstOrder_piece_normSq_le (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ' ρ
        (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg) i
        (C2 i) (Real.sqrt Λcom) (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λpb))
        (∑ n ∈ Finset.range (i + 1), Q n) ((Module.finrank ℝ E : ℝ) ^ 2 * Fpb i)
        (hC2_nn i) hFS hFT
        (hC2 i hi _ _ (Real.sqrt Λcom) (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λpb))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hS0 hT0)
      refine le_trans hmaster (le_of_eq ?_)
      rw [Real.sq_sqrt hΛcom_nn, Real.sq_sqrt (mul_nonneg (by positivity) hΛpb_nn)]
  · have hIsE := not_nonempty_iff.mp hM
    refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
    have h0 := lieFirstOrder_norm_isEmpty (I := I) (M := M) hIsE g₀ 3 (2 + i)
      (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ' ρ
          (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)))
    rw [h0]
    norm_num

theorem lieFirstOrderPiece_connectionDifference_metricPerturbationPath_riemannianFiberNormSq_order0_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((deTurckLieTraceCoeffPiece (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (connectionDifferenceSection (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
                  g₀)).toSection x) ≤ Λ := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_metricPerturbationPath_riemannianFiberNormSq_ballUniform (I := I) (M := M) g₀ a (R := R) hδ₀
    obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
      lieFirstOrder_connectionDifference_bounds (I := I) (M := M) g₀ a ha_super hR hδ₀
    refine ⟨Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * Λcd),
      mul_nonneg hΛcom_nn (mul_nonneg (by positivity) hΛcd_nn), ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x
    have := hM
    obtain ⟨htie, hδP, hδP_le⟩ :=
      lieFirstOrder_metricPerturbationPath_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
    have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
      lieFirstOrder_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
    have hPball := lieFirstOrder_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
      hTball hT'ball hs
    obtain ⟨hcd0, _⟩ := hcd (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
    refine le_trans (lieFirstOrder_piece_riemannianFiberNormSq_le (I := I) (M := M) g₀
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ' ρ
      (connectionDifferenceSection (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g₀) x) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckLieTraceCoeff (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤ Λcom := by
      rw [lieFirstOrder_riemannianFiberNormSq_dLTC_toSection_eq]
      exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
    have h2 : (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((connectionDifferenceSection (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
            g₀).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * Λcd :=
      mul_le_mul_of_nonneg_left (hcd0 x) (by positivity)
    refine mul_le_mul h1 h2 ?_ hΛcom_nn
    exact mul_nonneg (by positivity)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 2 x _)
  · have hIsE := not_nonempty_iff.mp hM
    exact ⟨0, le_rfl, fun T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x =>
      (hIsE.false x).elim⟩

theorem lieFirstOrderPiece_connectionDifferenceBackground_metricPerturbationPath_riemannianFiberNormSq_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((deTurckLieTraceCoeffPiece (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀
                  (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)).toSection x) ≤ Λ := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_metricPerturbationPath_riemannianFiberNormSq_ballUniform (I := I) (M := M) g₀ a (R := R) hδ₀
    obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
      lieFirstOrder_connectionDifference_bounds (I := I) (M := M) g₀ a ha_super hR hδ₀
    obtain ⟨Λfx, hΛfx_nn, hΛfx⟩ :=
      exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 2
        (lieFirstOrderFixCd (I := I) (M := M) g₀ g_bg)
    refine ⟨Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx)),
      mul_nonneg hΛcom_nn (mul_nonneg (by positivity) (by linarith)), ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x
    have := hM
    obtain ⟨htie, hδP, hδP_le⟩ :=
      lieFirstOrder_metricPerturbationPath_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
    have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
      lieFirstOrder_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
    have hPball := lieFirstOrder_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
      hTball hT'ball hs
    obtain ⟨hcd0, _⟩ := hcd (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
    refine le_trans (lieFirstOrder_piece_riemannianFiberNormSq_le (I := I) (M := M) g₀
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ' ρ
      (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg) x) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckLieTraceCoeff (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤ Λcom := by
      rw [lieFirstOrder_riemannianFiberNormSq_dLTC_toSection_eq]
      exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
    have hΨ0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
        ((deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤
        2 * Λcd + 2 * Λfx := by
      rw [lieFirstOrder_connectionDifferenceBackground_decomp (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg]
      refine le_trans (lieFirstOrder_riemannianFiberNormSq_toSection_add_le (I := I) (M := M) g₀ 1 2 _ _ x) ?_
      have h2 := hcd0 x
      have h3 := hΛfx x
      linarith
    have h2 : (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx) :=
      mul_le_mul_of_nonneg_left hΨ0 (by positivity)
    refine mul_le_mul h1 h2 ?_ hΛcom_nn
    exact mul_nonneg (by positivity)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 2 x _)
  · have hIsE := not_nonempty_iff.mp hM
    exact ⟨0, le_rfl, fun T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x =>
      (hIsE.false x).elim⟩

theorem lieFirstOrderPiece_psiB_metricPerturbationPath_riemannianFiberNormSq_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((deTurckLieTraceCoeffPiece (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀
                  (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)).toSection x) ≤ Λ := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_metricPerturbationPath_riemannianFiberNormSq_ballUniform (I := I) (M := M) g₀ a (R := R) hδ₀
    obtain ⟨Λpb, Fpb, hΛpb_nn, hFpb_nn, hpb⟩ :=
      lieFirstOrder_backgroundCoefficient_bounds (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
    refine ⟨Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * Λpb),
      mul_nonneg hΛcom_nn (mul_nonneg (by positivity) hΛpb_nn), ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x
    have := hM
    obtain ⟨htie, hδP, hδP_le⟩ :=
      lieFirstOrder_metricPerturbationPath_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
    have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
      lieFirstOrder_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
    have hPball := lieFirstOrder_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
      hTball hT'ball hs
    obtain ⟨hpb0, _⟩ := hpb (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
    refine le_trans (lieFirstOrder_piece_riemannianFiberNormSq_le (I := I) (M := M) g₀
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ' ρ
      (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg) x) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckLieTraceCoeff (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤ Λcom := by
      rw [lieFirstOrder_riemannianFiberNormSq_dLTC_toSection_eq]
      exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
    have h2 : (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * Λpb :=
      mul_le_mul_of_nonneg_left (hpb0 x) (by positivity)
    refine mul_le_mul h1 h2 ?_ hΛcom_nn
    exact mul_nonneg (by positivity)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 2 x _)
  · have hIsE := not_nonempty_iff.mp hM
    exact ⟨0, le_rfl, fun T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x =>
      (hIsE.false x).elim⟩

private theorem lieFirstOrder_norm_sq_le_of_norm_le {V : Type*} [SeminormedAddCommGroup V]
    {v : V} {S : ℝ} (h : ‖v‖ ≤ S) : ‖v‖ ^ 2 ≤ S ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg v) h 2

private theorem lieFirstOrder_norm_le_sqrt {V : Type*} [SeminormedAddCommGroup V]
    {v : V} {P : ℝ} (h : ‖v‖ ^ 2 ≤ P) : ‖v‖ ≤ Real.sqrt P := by
  have h1 : ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
  rw [h1]
  exact Real.sqrt_le_sqrt h

theorem deTurckLieFirstOrderCoeff_metricPerturbationPath_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (deTurckLieFirstOrderCoeff (I := I) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤ P i := by
  obtain ⟨Pc, hPc_nn, hPc⟩ :=
    lieFirstOrderPiece_connectionDifference_metricPerturbationPath_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨Pbg, hPbg_nn, hPbg⟩ :=
    lieFirstOrderPiece_connectionDifferenceBackground_metricPerturbationPath_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨Pb, hPb_nn, hPb⟩ :=
    lieFirstOrderPiece_psiB_metricPerturbationPath_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨fun i => (11 * Real.sqrt (Pc i) + 2 * Real.sqrt (Pb i) + Real.sqrt (Pbg i)) ^ 2,
    fun i => sq_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  set g₁ : SmoothRiemannianMetric I M := metricPerturbationPath (I := I) g₀ T T' hδ hδ' s with hg₁
  have hcd : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ (connectionDifferenceSection (I := I) g₁ g₀))‖ ≤
        Real.sqrt (Pc i) := fun σ' ρ =>
    lieFirstOrder_norm_le_sqrt (hPc T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs)
  have hbg : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ
          (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀ g₁ g_bg))‖ ≤
        Real.sqrt (Pbg i) := fun σ' ρ =>
    lieFirstOrder_norm_le_sqrt (hPbg T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs)
  have hpb : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ
          (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg))‖ ≤
        Real.sqrt (Pb i) := fun σ' ρ =>
    lieFirstOrder_norm_le_sqrt (hPb T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs)
  rw [deTurckLieFirstOrderCoeff_eq_lieFirstOrderPiece_sum (I := I) (M := M) g₀ g₁ g_bg]
  simp only [iteratedCovGrad_add, iteratedCovGrad_sub]
  refine lieFirstOrder_norm_sq_le_of_norm_le ?_
  have hsqrtPc_nn : 0 ≤ Real.sqrt (Pc i) := Real.sqrt_nonneg _
  have hsqrtPb_nn : 0 ≤ Real.sqrt (Pb i) := Real.sqrt_nonneg _
  have hblock1 := DifferentialGeometry.Analysis.norm_add_sub_sub_sub_sub_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaA (Equiv.refl (Fin 3))
        (connectionDifferenceSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaA (Equiv.refl (Fin 3))
        (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaC (Equiv.refl (Fin 3))
        (connectionDifferenceSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaD lieFirstOrderRhoSlot0
        (connectionDifferenceSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieFirstOrderRhoSlot1
        (connectionDifferenceSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaF (Equiv.refl (Fin 3))
        (connectionDifferenceSection (I := I) g₁ g₀)))
  have hblock2 := DifferentialGeometry.Analysis.norm_add_sub_sub_sub_sub_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaASwap (Equiv.refl (Fin 3))
        (connectionDifferenceSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaASwap (Equiv.refl (Fin 3))
        (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaCSwap (Equiv.refl (Fin 3))
        (connectionDifferenceSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaDSwap lieFirstOrderRhoSlot0
        (connectionDifferenceSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaESwap lieFirstOrderRhoSlot1
        (connectionDifferenceSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaFSwap (Equiv.refl (Fin 3))
        (connectionDifferenceSection (I := I) g₁ g₀)))
  have htri1 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaC lieFirstOrderRhoSlot0
          (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀ g₁ g_bg))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaA (Equiv.refl (Fin 3))
            (connectionDifferenceSection (I := I) g₁ g₀))
        + iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaA (Equiv.refl (Fin 3))
            (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaC (Equiv.refl (Fin 3))
            (connectionDifferenceSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaD lieFirstOrderRhoSlot0
            (connectionDifferenceSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieFirstOrderRhoSlot1
            (connectionDifferenceSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaF (Equiv.refl (Fin 3))
            (connectionDifferenceSection (I := I) g₁ g₀)))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaASwap (Equiv.refl (Fin 3))
            (connectionDifferenceSection (I := I) g₁ g₀))
        + iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaASwap (Equiv.refl (Fin 3))
            (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaCSwap (Equiv.refl (Fin 3))
            (connectionDifferenceSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaDSwap lieFirstOrderRhoSlot0
            (connectionDifferenceSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaESwap lieFirstOrderRhoSlot1
            (connectionDifferenceSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaFSwap (Equiv.refl (Fin 3))
            (connectionDifferenceSection (I := I) g₁ g₀))))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieFirstOrderRhoSlot0
        (connectionDifferenceSection (I := I) g₁ g₀)))
  have htri2 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaC lieFirstOrderRhoSlot0
          (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀ g₁ g_bg))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaA (Equiv.refl (Fin 3))
            (connectionDifferenceSection (I := I) g₁ g₀))
        + iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaA (Equiv.refl (Fin 3))
            (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaC (Equiv.refl (Fin 3))
            (connectionDifferenceSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaD lieFirstOrderRhoSlot0
            (connectionDifferenceSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieFirstOrderRhoSlot1
            (connectionDifferenceSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaF (Equiv.refl (Fin 3))
            (connectionDifferenceSection (I := I) g₁ g₀))))
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaASwap (Equiv.refl (Fin 3))
          (connectionDifferenceSection (I := I) g₁ g₀))
      + iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaASwap (Equiv.refl (Fin 3))
          (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaCSwap (Equiv.refl (Fin 3))
          (connectionDifferenceSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaDSwap lieFirstOrderRhoSlot0
          (connectionDifferenceSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaESwap lieFirstOrderRhoSlot1
          (connectionDifferenceSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaFSwap (Equiv.refl (Fin 3))
          (connectionDifferenceSection (I := I) g₁ g₀)))
  have htri3 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaC lieFirstOrderRhoSlot0
        (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaA (Equiv.refl (Fin 3))
          (connectionDifferenceSection (I := I) g₁ g₀))
      + iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaA (Equiv.refl (Fin 3))
          (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaC (Equiv.refl (Fin 3))
          (connectionDifferenceSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaD lieFirstOrderRhoSlot0
          (connectionDifferenceSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieFirstOrderRhoSlot1
          (connectionDifferenceSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaF (Equiv.refl (Fin 3))
          (connectionDifferenceSection (I := I) g₁ g₀)))
  have h1 := hcd lieFirstOrderSigmaA (Equiv.refl (Fin 3))
  have h2 := hpb lieFirstOrderSigmaA (Equiv.refl (Fin 3))
  have h3 := hcd lieFirstOrderSigmaC (Equiv.refl (Fin 3))
  have h4 := hcd lieFirstOrderSigmaD lieFirstOrderRhoSlot0
  have h5 := hcd (Equiv.refl (Fin 4)) lieFirstOrderRhoSlot1
  have h6 := hcd lieFirstOrderSigmaF (Equiv.refl (Fin 3))
  have h7 := hcd lieFirstOrderSigmaASwap (Equiv.refl (Fin 3))
  have h8 := hpb lieFirstOrderSigmaASwap (Equiv.refl (Fin 3))
  have h9 := hcd lieFirstOrderSigmaCSwap (Equiv.refl (Fin 3))
  have h10 := hcd lieFirstOrderSigmaDSwap lieFirstOrderRhoSlot0
  have h11 := hcd lieFirstOrderSigmaESwap lieFirstOrderRhoSlot1
  have h12 := hcd lieFirstOrderSigmaFSwap (Equiv.refl (Fin 3))
  have h13 := hbg lieFirstOrderSigmaC lieFirstOrderRhoSlot0
  have h14 := hcd (Equiv.refl (Fin 4)) lieFirstOrderRhoSlot0
  linarith [htri1, htri2, htri3, hblock1, hblock2]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lieFirstOrder_riemannianFiberNormSq_sub_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a - b) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x a +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b := by
  rw [sub_eq_add_neg]
  have h := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x a (-b)
  rw [lieFirstOrder_riemannianFiberNormSq_neg (I := I) (M := M) g r s x b] at h
  exact h

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lieFirstOrder_riemannianFiberNormSq_block6_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (b1 b2 b3 b4 b5 b6 : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (b1 - b2 - b3 - b4 - b5 - b6) ≤
      32 * riemannianFiberNormSq (I := I) (M := M) g r s x b1 +
        32 * riemannianFiberNormSq (I := I) (M := M) g r s x b2 +
        16 * riemannianFiberNormSq (I := I) (M := M) g r s x b3 +
        8 * riemannianFiberNormSq (I := I) (M := M) g r s x b4 +
        4 * riemannianFiberNormSq (I := I) (M := M) g r s x b5 +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b6 := by
  have h6 := lieFirstOrder_riemannianFiberNormSq_sub_le (I := I) (M := M) g r s x (b1 - b2 - b3 - b4 - b5) b6
  have h5 := lieFirstOrder_riemannianFiberNormSq_sub_le (I := I) (M := M) g r s x (b1 - b2 - b3 - b4) b5
  have h4 := lieFirstOrder_riemannianFiberNormSq_sub_le (I := I) (M := M) g r s x (b1 - b2 - b3) b4
  have h3 := lieFirstOrder_riemannianFiberNormSq_sub_le (I := I) (M := M) g r s x (b1 - b2) b3
  have h2 := lieFirstOrder_riemannianFiberNormSq_sub_le (I := I) (M := M) g r s x b1 b2
  have hn5 := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x b5
  have hn6 := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x b6
  linarith

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lieFirstOrder_riemannianFiberNormSq_block6_le' (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (b1 b2 b3 b4 b5 b6 : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (b1 + b2 - b3 - b4 - b5 - b6) ≤
      32 * riemannianFiberNormSq (I := I) (M := M) g r s x b1 +
        32 * riemannianFiberNormSq (I := I) (M := M) g r s x b2 +
        16 * riemannianFiberNormSq (I := I) (M := M) g r s x b3 +
        8 * riemannianFiberNormSq (I := I) (M := M) g r s x b4 +
        4 * riemannianFiberNormSq (I := I) (M := M) g r s x b5 +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b6 := by
  have h6 := lieFirstOrder_riemannianFiberNormSq_sub_le (I := I) (M := M) g r s x (b1 + b2 - b3 - b4 - b5) b6
  have h5 := lieFirstOrder_riemannianFiberNormSq_sub_le (I := I) (M := M) g r s x (b1 + b2 - b3 - b4) b5
  have h4 := lieFirstOrder_riemannianFiberNormSq_sub_le (I := I) (M := M) g r s x (b1 + b2 - b3) b4
  have h3 := lieFirstOrder_riemannianFiberNormSq_sub_le (I := I) (M := M) g r s x (b1 + b2) b3
  have h2 := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x b1 b2
  have hn5 := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x b5
  have hn6 := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x b6
  linarith

theorem deTurckLieFirstOrderCoeff_metricPerturbationPath_riemannianFiberNormSq_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((deTurckLieFirstOrderCoeff (I := I) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤ Λ := by
  obtain ⟨Λc, hΛc_nn, hΛc⟩ :=
    lieFirstOrderPiece_connectionDifference_metricPerturbationPath_riemannianFiberNormSq_order0_ballUniform (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨Λbg, hΛbg_nn, hΛbg⟩ :=
    lieFirstOrderPiece_connectionDifferenceBackground_metricPerturbationPath_riemannianFiberNormSq_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨Λb, hΛb_nn, hΛb⟩ :=
    lieFirstOrderPiece_psiB_metricPerturbationPath_riemannianFiberNormSq_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨8 * Λbg + 800 * Λc + 400 * Λb, by linarith, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  set g₁ : SmoothRiemannianMetric I M := metricPerturbationPath (I := I) g₀ T T' hδ hδ' s with hg₁
  have hcd : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        ((deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ
          (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) ≤ Λc := fun σ' ρ =>
    hΛc T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ s hs x
  have hbg : riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
      ((deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaC lieFirstOrderRhoSlot0
        (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ Λbg :=
    hΛbg T T' hδ_le hδ hδ'_le hδ' hTball hT'ball lieFirstOrderSigmaC lieFirstOrderRhoSlot0 s hs x
  have hpb : ∀ (σ' : Equiv.Perm (Fin 4)),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        ((deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' (Equiv.refl (Fin 3))
          (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ Λb := fun σ' =>
    hΛb T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' (Equiv.refl (Fin 3)) s hs x
  have hsec := congrArg (fun (W : SmoothCcTensor g₀ 3 2) =>
      (show TensorRSSpace 3 2 I x from W.toSection x))
    (deTurckLieFirstOrderCoeff_eq_lieFirstOrderPiece_sum (I := I) (M := M) g₀ g₁ g_bg)
  simp only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_add, ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply] at hsec
  rw [hsec]
  set A := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaC lieFirstOrderRhoSlot0
      (deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
  set B1 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaA (Equiv.refl (Fin 3))
      (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)
  set B2 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaA (Equiv.refl (Fin 3))
      (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
  set B3 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaC (Equiv.refl (Fin 3))
      (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)
  set B4 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaD lieFirstOrderRhoSlot0
      (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)
  set B5 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieFirstOrderRhoSlot1
      (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)
  set B6 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaF (Equiv.refl (Fin 3))
      (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)
  set C1 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaASwap (Equiv.refl (Fin 3))
      (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)
  set C2 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaASwap (Equiv.refl (Fin 3))
      (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
  set C3 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaCSwap (Equiv.refl (Fin 3))
      (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)
  set C4 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaDSwap lieFirstOrderRhoSlot0
      (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)
  set C5 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaESwap lieFirstOrderRhoSlot1
      (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)
  set C6 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieFirstOrderSigmaFSwap (Equiv.refl (Fin 3))
      (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)
  set Dz := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieFirstOrderRhoSlot0
      (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)
  have houter1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 2 x
    (A + (B1 + B2 - B3 - B4 - B5 - B6) + (C1 + C2 - C3 - C4 - C5 - C6)) Dz
  have houter2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 2 x
    (A + (B1 + B2 - B3 - B4 - B5 - B6)) (C1 + C2 - C3 - C4 - C5 - C6)
  have houter3 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 2 x
    A (B1 + B2 - B3 - B4 - B5 - B6)
  have hblkB := lieFirstOrder_riemannianFiberNormSq_block6_le' (I := I) (M := M) g₀ 3 2 x B1 B2 B3 B4 B5 B6
  have hblkC := lieFirstOrder_riemannianFiberNormSq_block6_le' (I := I) (M := M) g₀ 3 2 x C1 C2 C3 C4 C5 C6
  have e1 := hcd lieFirstOrderSigmaA (Equiv.refl (Fin 3))
  have e2 := hpb lieFirstOrderSigmaA
  have e3 := hcd lieFirstOrderSigmaC (Equiv.refl (Fin 3))
  have e4 := hcd lieFirstOrderSigmaD lieFirstOrderRhoSlot0
  have e5 := hcd (Equiv.refl (Fin 4)) lieFirstOrderRhoSlot1
  have e6 := hcd lieFirstOrderSigmaF (Equiv.refl (Fin 3))
  have e7 := hcd lieFirstOrderSigmaASwap (Equiv.refl (Fin 3))
  have e8 := hpb lieFirstOrderSigmaASwap
  have e9 := hcd lieFirstOrderSigmaCSwap (Equiv.refl (Fin 3))
  have e10 := hcd lieFirstOrderSigmaDSwap lieFirstOrderRhoSlot0
  have e11 := hcd lieFirstOrderSigmaESwap lieFirstOrderRhoSlot1
  have e12 := hcd lieFirstOrderSigmaFSwap (Equiv.refl (Fin 3))
  have e14 := hcd (Equiv.refl (Fin 4)) lieFirstOrderRhoSlot0
  linarith [houter1, houter2, houter3, hblkB, hblkC, hbg, hΛc_nn, hΛb_nn, hΛbg_nn]

end DifferentialGeometry.Analysis.Sobolev

end
