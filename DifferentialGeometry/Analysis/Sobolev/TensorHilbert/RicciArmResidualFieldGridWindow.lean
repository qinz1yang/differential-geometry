import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldInputSlotSymmetrization
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.FlatArmCoeffConnectionDifferenceBridge
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindowGInvQuadResidual
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindowBgRefoldConversion
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section NormedScalarHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma riemannianFiberNormSq_smul_value (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (x : M) (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

end NormedScalarHelpers


theorem riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0BgRCommCoeffDiff_gridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
                - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)).toSection x)
                  ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_rfns_icg_mvDoubleTraceField_window (I := I) (M := M) g₀ 2 hδ₀
  set KD : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + u)
      (iteratedCovGrad (I := I) g₀ 4 2 u (cometricDoubleTraceField (I := I) g₀ 2))).choose
    with hKD_def
  have hKD_nn : ∀ u, 0 ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + u)
      (iteratedCovGrad (I := I) g₀ 4 2 u
        (cometricDoubleTraceField (I := I) g₀ 2))).choose_spec.1
  have hKD : ∀ u (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) y
          ((iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection y) ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + u)
      (iteratedCovGrad (I := I) g₀ 4 2 u
        (cometricDoubleTraceField (I := I) g₀ 2))).choose_spec.2
  set KW : ℕ → ℝ := fun w =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + w)
      (iteratedCovGrad (I := I) g₀ 2 4 w
        (riemannCometricDoubleTraceFold (I := I) (M := M) g₀))).choose
    with hKW_def
  have hKW_nn : ∀ w, 0 ≤ KW w := fun w =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + w)
      (iteratedCovGrad (I := I) g₀ 2 4 w
        (riemannCometricDoubleTraceFold (I := I) (M := M) g₀))).choose_spec.1
  have hKW : ∀ w (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + w) y
          ((iteratedCovGrad (I := I) g₀ 2 4 w
            (riemannCometricDoubleTraceFold (I := I) (M := M) g₀)).toSection y) ≤ KW w := fun w =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + w)
      (iteratedCovGrad (I := I) g₀ 2 4 w
        (riemannCometricDoubleTraceFold (I := I) (M := M) g₀))).choose_spec.2
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      ∑ u ∈ Finset.range (i + 1), (2 * C2 u + 2 * KD u) *
        ∑ w ∈ Finset.range (i + 1 - u), KW w,
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun u _ => mul_nonneg
        (by have := hC2_nn u; have := hKD_nn u; linarith)
        (Finset.sum_nonneg fun w _ => hKW_nn w)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hdiff : ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
      - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
        (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2 - cometricDoubleTraceField
          (I := I) g₀ 2)
        (riemannCometricDoubleTraceFold (I := I) (M := M) g₀) := by
    rw [appCcRS_sub_left (I := I) (M := M) g₀ 2 4 2
      (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)
        (cometricDoubleTraceField (I := I) g₀ 2)
      (riemannCometricDoubleTraceFold (I := I) (M := M) g₀)]
    rw [← bgRCommCoeffField_eq_refold (I := I) (M := M) g₀ g₁]
    rw [← mvDoubleTraceField_self_eq (I := I) (M := M) g₀ 2]
    rw [← bgRCommCoeffField_eq_refold (I := I) (M := M) g₀ g₀]
  rw [hdiff]
  refine le_trans
    (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I)
    (M := M) g₀ i 2 4 2
    (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2 - cometricDoubleTraceField
      (I := I) g₀ 2)
    (riemannCometricDoubleTraceFold (I := I) (M := M) g₀) x) ?_
  have hW_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) :=
    Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
  have hAd : ∀ u : ℕ, u ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 4 2 u
            (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2
              - cometricDoubleTraceField (I := I) g₀ 2)).toSection x) ≤
        (2 * C2 u + 2 * KD u) * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
    intro u hu
    have hsec : (iteratedCovGrad (I := I) g₀ 4 2 u
        (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2
          - cometricDoubleTraceField (I := I) g₀ 2)).toSection x =
        (iteratedCovGrad (I := I) g₀ 4 2 u
          (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection x -
        (iteratedCovGrad (I := I) g₀ 4 2 u
          (cometricDoubleTraceField (I := I) g₀ 2)).toSection x := by
      rw [sub_eq_add_neg (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)
        (cometricDoubleTraceField (I := I) g₀ 2)]
      rw [iteratedCovGrad_add (I := I) g₀ 4 2 u _ _,
        iteratedCovGrad_neg (I := I) g₀ 4 2 u _, SmoothCcTensor.toSection_add]
      rw [show (((iteratedCovGrad (I := I) g₀ 4 2 u
            (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection +
          (-(iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2))).toSection) x) =
          (iteratedCovGrad (I := I) g₀ 4 2 u
            (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection x +
          (-(iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2))).toSection x from rfl]
      rw [show ((-(iteratedCovGrad (I := I) g₀ 4 2 u
          (cometricDoubleTraceField (I := I) g₀ 2))).toSection x) =
          -((iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) from by
        rw [SmoothCcTensor.toSection_neg]; rfl]
      rw [← sub_eq_add_neg]
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_sub_le_pt (I := I) (M := M) g₀ 4 (2 + u) x _ _) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
        ((iteratedCovGrad (I := I) g₀ 4 2 u
          (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection x) ≤
        C2 u * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
      refine le_trans (hC2 g₁ P htie hδ_le hδ0 hbound u (i + 1) (by omega) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hC2_nn u)
      exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
        ((iteratedCovGrad (I := I) g₀ 4 2 u
          (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) ≤
        KD u * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
            ((iteratedCovGrad (I := I) g₀ 4 2 u
              (cometricDoubleTraceField (I := I) g₀ 2)).toSection x)
          ≤ KD u := hKD u x
        _ = KD u * 1 := by ring
        _ ≤ KD u * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
            refine mul_le_mul_of_nonneg_left ?_ (hKD_nn u)
            exact Combinatorics.one_le_boundedFactorGridWindow b hb_nn (by omega)
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 4 2 u
            (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection x)
        ≤ 2 * (C2 u * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
            2 * (KD u * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
          linarith [h1, h2]
      _ = (2 * C2 u + 2 * KD u) * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
          ring
  calc diagonalGridGrowthFactor (E := E) i *
        ∑ u ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
              ((iteratedCovGrad (I := I) g₀ 4 2 u
                (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2
                  - cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
            ∑ w ∈ Finset.range (i + 1 - u),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 2 4 w
                  (riemannCometricDoubleTraceFold (I := I) (M := M) g₀)).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1),
            ((2 * C2 u + 2 * KD u) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) *
            ∑ w ∈ Finset.range (i + 1 - u), KW w := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun u hu => ?_) (appCcGdiag_nonneg (E := E) i)
        rw [Finset.mem_range] at hu
        refine mul_le_mul (hAd u (by omega)) (Finset.sum_le_sum fun w _ => hKW w x)
          (Finset.sum_nonneg fun w _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (4 + w) x _)
          (mul_nonneg (by have := hC2_nn u; have := hKD_nn u; linarith) hW_nn)
    _ = (diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1), (2 * C2 u + 2 * KD u) *
            ∑ w ∈ Finset.range (i + 1 - u), KW w) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
        have hstep : ∀ u : ℕ, ((2 * C2 u + 2 * KD u) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) *
            (∑ w ∈ Finset.range (i + 1 - u), KW w) =
            ((2 * C2 u + 2 * KD u) * ∑ w ∈ Finset.range (i + 1 - u), KW w) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
          intro u
          ring
        rw [Finset.sum_congr rfl fun u _ => hstep u, ← Finset.sum_mul]
        ring


theorem rfns_iteratedCovGrad_ricciArmSharpGradKoszulResidualMetricDiff_gridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ :=
    exists_rfns_icg_mvPairTraceOp_window (I := I) (M := M) g₀ hδ₀
  obtain ⟨CW1, hCW1_nn, hCW1⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_koszulConnDiffFoldWeight_gridWindow_le (I := I)
      (M := M) g₀ tauM1 hδ₀
  obtain ⟨CW2, hCW2_nn, hCW2⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_koszulConnDiffFoldWeight_gridWindow_le (I := I)
      (M := M) g₀ tauM2 hδ₀
  obtain ⟨CW3, hCW3_nn, hCW3⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_koszulConnDiffFoldWeight_gridWindow_le (I := I)
      (M := M) g₀ tauM3 hδ₀
  obtain ⟨CW4, hCW4_nn, hCW4⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_koszulConnDiffFoldWeight_gridWindow_le (I := I)
      (M := M) g₀ tauM4 hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set CX : ℕ → ℝ := fun w =>
    fr ^ 2 * (4 * CW1 w + 4 * CW2 w + 4 * CW3 w + 4 * CW4 w) with hCX_def
  have hCX_nn : ∀ w, 0 ≤ CX w := fun w => by
    have h1 := hCW1_nn w
    have h2 := hCW2_nn w
    have h3 := hCW3_nn w
    have h4 := hCW4_nn w
    have h5 : (0 : ℝ) ≤ fr ^ 2 := by positivity
    simp only [hCX_def]
    nlinarith
  refine ⟨fun i => 4 * (diagonalGridGrowthFactor (E := E) i *
      ∑ u ∈ Finset.range (i + 1), CPT u *
        ∑ w ∈ Finset.range (i + 1 - u),
          CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3)),
    fun i => by
      refine mul_nonneg (by norm_num)
        (mul_nonneg (appCcGdiag_nonneg (E := E) i)
          (Finset.sum_nonneg fun u _ => mul_nonneg (hCPT_nn u)
            (Finset.sum_nonneg fun w _ => mul_nonneg (hCX_nn w)
              (Combinatorics.windowPairCellCount_nonneg _ _)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  rw [metricDifferenceCcTensor_eq_symmS (I := I) (M := M) g₀ g₁ P htie]
  rw [sharpGradKoszulResidualField_eq_refold (I := I) (M := M) g₀ g₁ P htie]
  have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
      ((2 : ℝ) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)))))).toSection x =
      (2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)))))).toSection x) := by
    rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (2 : ℝ) _,
      SmoothCcTensor.toSection_smul]
    rfl
  rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (2 : ℝ) _,
    show ((2 : ℝ)) ^ 2 = 4 from by norm_num]
  have hPT : ∀ u : ℕ, u ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 6 2 u
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) :=
    fun u hu => hCPT g₁ P htie hδ_le hδ0 hbound u (i + 1) (by omega) x
  have hWX : ∀ w : ℕ, w ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                    koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                  (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                    koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))))).toSection x) ≤
        CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
    intro w hw
    rw [riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6
      ricciFoldRemainderSlotPerm _ w x]
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
        ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)) =
        slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4
          ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))) from rfl]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
      (slotExtend (I := I) (M := M) g₀ 0 4
        ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))) w x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)) w x) hfr_nn) ?_
    have hsub : (iteratedCovGrad (I := I) g₀ 0 4 w
        ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x -
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x := by
      rw [sub_eq_add_neg (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)]
      rw [iteratedCovGrad_add (I := I) g₀ 0 4 w _ _,
        iteratedCovGrad_neg (I := I) g₀ 0 4 w _, SmoothCcTensor.toSection_add]
      rw [show (((iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection +
          (-(iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))).toSection) x) =
          (iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x +
          (-(iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))).toSection x from rfl]
      rw [show ((-(iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))).toSection x) =
          -((iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x) from by
        rw [SmoothCcTensor.toSection_neg]; rfl]
      rw [← sub_eq_add_neg]
    have h12 : (iteratedCovGrad (I := I) g₀ 0 4 w
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P)).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 0 4 w _ _, SmoothCcTensor.toSection_add]
      rfl
    have h34 : (iteratedCovGrad (I := I) g₀ 0 4 w
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P)).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 0 4 w _ _, SmoothCcTensor.toSection_add]
      rfl
    have hA1 := hCW1 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM1
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P from rfl] at hA1
    have hA2 := hCW2 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM2
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P from rfl] at hA2
    have hA3 := hCW3 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM3
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P from rfl] at hA3
    have hA4 := hCW4 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM4
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P from rfl] at hA4
    calc fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
              (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))).toSection x))
        ≤ fr * (fr * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          rw [hsub]
          exact riemannianFiberNormSq_sub_le_pt (I := I) (M := M) g₀ 0 (4 + w) x _ _
      _ ≤ fr * (fr *
          (2 * (2 * (CW1 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
              + 2 * (CW2 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)))
          + 2 * (2 * (CW3 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
              + 2 * (CW4 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          have hx12 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
              ((iteratedCovGrad (I := I) g₀ 0 4 w
                (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x) ≤
              2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 0 4 w
                  (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P)).toSection x)
              + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 0 4 w
                  (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x) := by
            rw [h12]
            exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + w) x _ _
          have hx34 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
              ((iteratedCovGrad (I := I) g₀ 0 4 w
                (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x) ≤
              2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 0 4 w
                  (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P)).toSection x)
              + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 0 4 w
                  (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x) := by
            rw [h34]
            exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + w) x _ _
          linarith [hA1, hA2, hA3, hA4, hx12, hx34]
      _ = CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
          simp only [hCX_def]
          ring
  refine le_trans (mul_le_mul_of_nonneg_left
    (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ i 2 6 2
      (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)))) x)
    (by norm_num : (0 : ℝ) ≤ 4)) ?_
  calc (4 : ℝ) * (diagonalGridGrowthFactor (E := E) i *
        ∑ u ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
              ((iteratedCovGrad (I := I) g₀ 6 2 u
                (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ w ∈ Finset.range (i + 1 - u),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
                ((iteratedCovGrad (I := I) g₀ 2 6 w
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁
                            tauM4 P))))).toSection x))
      ≤ 4 * (diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1),
            (CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1)) *
            ∑ w ∈ Finset.range (i + 1 - u),
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u hu => ?_)
            (appCcGdiag_nonneg (E := E) i)) (by norm_num)
        rw [Finset.mem_range] at hu
        refine mul_le_mul (hPT u (by omega)) (Finset.sum_le_sum fun w hw => ?_)
          (Finset.sum_nonneg fun w _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + w) x _)
          (mul_nonneg (hCPT_nn u)
            (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))
        rw [Finset.mem_range] at hw
        exact hWX w (by omega)
    _ ≤ 4 * ((diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1), CPT u *
            ∑ w ∈ Finset.range (i + 1 - u),
              CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun u hu => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun w hw => ?_
        rw [Finset.mem_range] at hu hw
        calc CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
            = (CPT u * CX w) *
                (Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)) := by ring
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 3) *
                  Combinatorics.boundedFactorGridWindow b (i + 1)
                    ((u + 1) + (w + 3) - 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn (i + 1) (u + 1)
                (w + 3) (by omega) (by omega)
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 3) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              refine mul_le_mul_of_nonneg_left ?_
                (Combinatorics.windowPairCellCount_nonneg _ _)
              exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
          _ = CPT u * (CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring
    _ = (4 * (diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1), CPT u *
            ∑ w ∈ Finset.range (i + 1 - u),
              CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3))) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring


theorem
    rfns_iteratedCovGrad_ricciArmRicciFoldRemainderFieldMetricDifference_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ :=
    exists_rfns_icg_mvPairTraceOp_window (I := I) (M := M) g₀ hδ₀
  obtain ⟨CWA, hCWA_nn, hCWA⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_ricciFoldWeightGeneral_boundedFactorGridWindow_le
      (I := I) (M := M) g₀
      (Equiv.swap (1 : Fin 6) 3) hδ₀
  obtain ⟨CWB, hCWB_nn, hCWB⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_ricciFoldWeightGeneral_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ ricciFoldWeightBPerm hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set CX : ℕ → ℝ := fun w => fr ^ 2 * (2 * CWA w + 2 * CWB w) with hCX_def
  have hCX_nn : ∀ w, 0 ≤ CX w := fun w => by
    have h1 := hCWA_nn w
    have h2 := hCWB_nn w
    have h3 : (0 : ℝ) ≤ fr ^ 2 := by positivity
    simp only [hCX_def]
    nlinarith
  refine ⟨fun i => (1 / 4 : ℝ) * (diagonalGridGrowthFactor (E := E) i *
      ∑ u ∈ Finset.range (i + 1), CPT u *
        ∑ w ∈ Finset.range (i + 1 - u),
          CX w * Combinatorics.windowPairCellCount (u + 1) (w + 1)),
    fun i => by
      refine mul_nonneg (by norm_num)
        (mul_nonneg (appCcGdiag_nonneg (E := E) i)
          (Finset.sum_nonneg fun u _ => mul_nonneg (hCPT_nn u)
            (Finset.sum_nonneg fun w _ => mul_nonneg (hCX_nn w)
              (Combinatorics.windowPairCellCount_nonneg _ _)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  rw [metricDifferenceCcTensor_eq_symmS (I := I) (M := M) g₀ g₁ P htie]
  rw [ricciFoldRemainderField_eq_refold (I := I) (M := M) g₀ g₁ (ccTensor02Symm (I := I) g₀ P)]
  have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
      ((-(1 / 2) : ℝ) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
                ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P)))))).toSection
                  x =
      (-(1 / 2) : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
                ricciFoldWeightB (I := I) (M := M) g₀
                  (ccTensor02Symm (I := I) g₀ P)))))).toSection x) := by
    rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (-(1 / 2) : ℝ) _,
      SmoothCcTensor.toSection_smul]
    rfl
  rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (-(1 / 2) : ℝ) _,
    show ((-(1 / 2) : ℝ)) ^ 2 = 1 / 4 from by norm_num]
  have hPT : ∀ u : ℕ, u ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 6 2 u
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) :=
    fun u hu => hCPT g₁ P htie hδ_le hδ0 hbound u (i + 1) (by omega) x
  have hWX : ∀ w : ℕ, w ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
                  ricciFoldWeightB (I := I) (M := M) g₀
                    (ccTensor02Symm (I := I) g₀ P))))).toSection x) ≤
        CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1) := by
    intro w hw
    rw [riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6
      ricciFoldRemainderSlotPerm _ w x]
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
          ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P)) =
        slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4
          (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
            ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))) from rfl]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
      (slotExtend (I := I) (M := M) g₀ 0 4
        (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
          ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))) w x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
          ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P)) w x) hfr_nn) ?_
    have hsplit : (iteratedCovGrad (I := I) g₀ 0 4 w
        (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
          ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 0 4 w _ _, SmoothCcTensor.toSection_add]
      rfl
    have hA := hCWA P hδ_le hδ0 hbound w (i + 1) (by omega) x
    have hB := hCWB P hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show (ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4
      (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 (Equiv.swap (1 : Fin 6) 3)
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
            (ccTensor02Symm (I := I) g₀ P)))) =
        ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) from rfl] at hA
    rw [show (ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4
      (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 ricciFoldWeightBPerm
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
            (ccTensor02Symm (I := I) g₀ P)))) =
        ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) from rfl] at hB
    calc fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
              ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))).toSection x))
        ≤ fr * (fr * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))).toSection
                x))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          rw [hsplit]
          exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + w) x _ _
      _ ≤ fr * (fr * (2 * (CWA w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1))
          + 2 * (CWB w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          have hnnA := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))).toSection x)
          linarith [hA, hB]
      _ = CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1) := by
          simp only [hCX_def]
          ring
  refine le_trans (mul_le_mul_of_nonneg_left
    (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ i 2 6 2
      (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
            ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P)))) x)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
  have hW_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) :=
    Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
  calc (1 / 4 : ℝ) * (diagonalGridGrowthFactor (E := E) i *
        ∑ u ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
              ((iteratedCovGrad (I := I) g₀ 6 2 u
                (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ w ∈ Finset.range (i + 1 - u),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
                ((iteratedCovGrad (I := I) g₀ 2 6 w
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
                        ricciFoldWeightB (I := I) (M := M) g₀
                          (ccTensor02Symm (I := I) g₀ P))))).toSection x))
      ≤ (1 / 4 : ℝ) * (diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1),
            (CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1)) *
            ∑ w ∈ Finset.range (i + 1 - u),
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1))) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u hu => ?_)
            (appCcGdiag_nonneg (E := E) i)) (by norm_num)
        rw [Finset.mem_range] at hu
        refine mul_le_mul (hPT u (by omega)) (Finset.sum_le_sum fun w hw => ?_)
          (Finset.sum_nonneg fun w _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + w) x _)
          (mul_nonneg (hCPT_nn u)
            (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))
        rw [Finset.mem_range] at hw
        exact hWX w (by omega)
    _ ≤ (1 / 4 : ℝ) * ((diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1), CPT u *
            ∑ w ∈ Finset.range (i + 1 - u),
              CX w * Combinatorics.windowPairCellCount (u + 1) (w + 1)) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun u hu => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun w hw => ?_
        rw [Finset.mem_range] at hu hw
        calc CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1))
            = (CPT u * CX w) *
                (Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1)) := by ring
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) ((u + 1) + (w + 1) - 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn (i + 1) (u + 1)
                (w + 1) (by omega) (by omega)
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              refine mul_le_mul_of_nonneg_left ?_
                (Combinatorics.windowPairCellCount_nonneg _ _)
              exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
          _ = CPT u * (CX w * Combinatorics.windowPairCellCount (u + 1) (w + 1)) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring
    _ = ((1 / 4 : ℝ) * (diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1), CPT u *
            ∑ w ∈ Finset.range (i + 1 - u),
              CX w * Combinatorics.windowPairCellCount (u + 1) (w + 1))) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
private theorem appCcRS_smul_left_local (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (k : ℝ) (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g a b c (k • Φ) W =
      k • ccOperatorFieldComp (I := I) (M := M) g a b c Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((k • ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection x) =
      k • (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [appCcRS_toSection, appCcRS_toSection]
  rw [show ((k • Φ).toSection x : TensorRSSpace b c I x) = k • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
@[simp] private theorem appCcRS_ccSlotSwapField_involutive (g : SmoothRiemannianMetric I M)
    (C : SmoothCcTensor g 2 2) :
    ccOperatorFieldComp (I := I) (M := M) g 2 2 2
        (ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C (ccInputSlotSwapField (I := I) (M := M) g))
        (ccInputSlotSwapField (I := I) (M := M) g) = C := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCcRS_toSection, appCcRS_toSection]
  apply ContinuousLinearMap.ext
  intro D
  simp only [ContinuousLinearMap.comp_apply]
  refine congrArg _ ?_
  change inputSlotSwapFib (I := I) (M := M) x (inputSlotSwapFib (I := I) (M := M) x D) = D
  rw [slotSwapFib_apply, slotSwapFib_apply, Tensor0SSpace.toModel_ofModel]
  rw [show ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel (𝕜 := ℝ) D)) = Tensor0SSpace.toModel (𝕜 := ℝ) D from by
    ext m
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext i
    exact congrArg m (Equiv.swap_apply_self (0 : Fin 2) 1 i)]
  exact Tensor0SSpace.ofModel_toModel D


theorem rfns_iteratedCovGrad_bgRDiffRefoldRemainderFieldInputSymm_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSlotSymm (I := I) (M := M) g₀
                (backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀
                  g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0BgRCommCoeffDiff_gridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    rfns_iteratedCovGrad_ricciArmSharpGradKoszulResidualMetricDiff_gridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨C₃, hC₃_nn, hC₃⟩ :=
    rfns_iteratedCovGrad_ricciArmRicciFoldRemainderFieldMetricDifference_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  have hSW_ex : ∀ q : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 2 q
          (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) ≤ c := fun q =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + q)
      (iteratedCovGrad (I := I) g₀ 2 2 q (ccInputSlotSwapField (I := I) (M := M) g₀))
  choose SW hSW_nn hSW using hSW_ex
  set CB : ℕ → ℝ := fun n => 4 * C₁ n + 4 * C₂ n + 2 * C₃ n with hCB_def
  have hCB_nn : ∀ n, 0 ≤ CB n := by
    intro n
    have h1 := hC₁_nn n
    have h2 := hC₂_nn n
    have h3 := hC₃_nn n
    simp only [hCB_def]
    linarith
  refine ⟨fun i => (1 / 2 : ℝ) * CB i +
      (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), CB i') *
        (∑ l ∈ Finset.range (i + 1), SW l)), ?_, ?_⟩
  · intro i
    have h2 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), CB i' := Finset.sum_nonneg fun i' _ => hCB_nn i'
    have h3 : 0 ≤ ∑ l ∈ Finset.range (i + 1), SW l := Finset.sum_nonneg fun l _ => hSW_nn l
    have h4 : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
    have h1 : 0 ≤ CB i := hCB_nn i
    positivity
  · intro g₁ P htie δ hδ_le hδ0 hbound i x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
    have hb_nn : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set W : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hW_def
    have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
    set BD : SmoothCcTensor g₀ 2 2 :=
      (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
          - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
        + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
            (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)
        - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
            (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁) with hBD_def
    have hB : ∀ n : ℕ, n ≤ i →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n BD).toSection x) ≤
        CB n * W := by
      intro n hn
      have hwin : Combinatorics.boundedFactorGridWindow b (n + 1) (n + 3) ≤ W := by
        rw [hW_def]
        exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (by omega)
      have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
              - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C₁ n * W :=
        le_trans (hC₁ g₁ P htie hδ_le hδ0 hbound n x)
          (mul_le_mul_of_nonneg_left hwin (hC₁_nn n))
      have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
              (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C₂ n * W :=
        le_trans (hC₂ g₁ P htie hδ_le hδ0 hbound n x)
          (mul_le_mul_of_nonneg_left hwin (hC₂_nn n))
      have h3 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
              (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C₃ n * W :=
        le_trans (hC₃ g₁ P htie hδ_le hδ0 hbound n x)
          (mul_le_mul_of_nonneg_left hwin (hC₃_nn n))
      have h2' : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            ((1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
              (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C₂ n * W := by
        rw [iteratedCovGrad_smul_real,
          show ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 n
              (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x =
            (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 2 2 n
              (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x from by
            rw [SmoothCcTensor.toSection_smul]; rfl,
          riemannianFiberNormSq_smul_value,
          show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
        have hnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
              (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x)
        linarith [h2]
      have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 n BD).toSection x =
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
              - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)).toSection x
          + (iteratedCovGrad (I := I) g₀ 2 2 n
              ((1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x)
          - (iteratedCovGrad (I := I) g₀ 2 2 n
              (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x := by
        rw [hBD_def, iteratedCovGrad_sub, iteratedCovGrad_add,
          SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add]
        rfl
      rw [hsplit]
      have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
            - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 n
            ((1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
              (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x)
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
            (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x)
      have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
            - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)).toSection x)
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          ((1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
            (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x)
      have hCBW : CB n * W = 4 * (C₁ n * W) + 4 * (C₂ n * W) + 2 * (C₃ n * W) := by
        simp only [hCB_def]
        ring
      refine le_trans hsub ?_
      rw [hCBW]
      linarith [hadd, h1, h2', h3]
    have hsubject : ccInputSlotSymm (I := I) (M := M) g₀
        (backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁) =
        (1 / 2 : ℝ) • (BD
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 BD
            (ccInputSlotSwapField (I := I) (M := M) g₀)) := by
      rw [show ccInputSlotSymm (I := I) (M := M) g₀
          (backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁) =
          (1 / 2 : ℝ) • (backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
              (backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁)
              (ccInputSlotSwapField (I := I) (M := M) g₀)) from rfl]
      refine congrArg (fun t => (1 / 2 : ℝ) • t) ?_
      rw [hBD_def]
      rw [show backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁ =
          ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
              (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
                - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
              (ccInputSlotSwapField (I := I) (M := M) g₀)
            + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)
            - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁) from rfl]
      simp only [appCcRS_sub_left, appCcRS_add_left, appCcRS_smul_left_local,
        appCcRS_ccSlotSwapField_involutive]
      abel
    rw [hsubject]
    have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
        ((1 / 2 : ℝ) • (BD
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 BD
            (ccInputSlotSwapField (I := I) (M := M) g₀)))).toSection x =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (BD
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 BD
              (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) := by
      rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
        SmoothCcTensor.toSection_smul]
      rfl
    rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
      show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
    have hsplit2 : (iteratedCovGrad (I := I) g₀ 2 2 i
        (BD
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 BD
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i BD).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 BD
              (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
      rfl
    rw [hsplit2]
    refine le_trans (mul_le_mul_of_nonneg_left
      (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
    have hQi : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i BD).toSection x) ≤ CB i * W :=
      hB i (le_refl i)
    have hApp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 BD
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
        diagonalGridGrowthFactor (E := E) i * ((∑ i' ∈ Finset.range (i + 1), CB i') *
          ((∑ l ∈ Finset.range (i + 1), SW l) * W)) := by
      refine le_trans
        (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
        (I := I) (M := M) g₀ i 2 2 2 BD
        (ccInputSlotSwapField (I := I) (M := M) g₀) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i' hi' => ?_
      rw [Finset.mem_range] at hi'
      have hswapsum : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1), SW l := by
        refine le_trans (Finset.sum_le_sum fun l _ => hSW l x) ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega)) ?_
        exact fun l _ _ => hSW_nn l
      have hBi' := hB i' (by omega)
      have hswap_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 2 2 i' BD).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l
                  (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)
          ≤ (CB i' * W) * (∑ l ∈ Finset.range (i + 1), SW l) :=
            mul_le_mul hBi' hswapsum hswap_nn (mul_nonneg (hCB_nn i') hW_nn)
        _ = CB i' * ((∑ l ∈ Finset.range (i + 1), SW l) * W) := by ring
    calc (1 / 4 : ℝ) * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i BD).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 BD
                (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x))
        ≤ (1 / 4 : ℝ) * (2 * (CB i * W)
            + 2 * (diagonalGridGrowthFactor (E := E) i * ((∑ i' ∈ Finset.range (i + 1), CB i') *
              ((∑ l ∈ Finset.range (i + 1), SW l) * W)))) := by
          nlinarith [hQi, hApp]
      _ = ((1 / 2 : ℝ) * CB i +
            (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i *
              (∑ i' ∈ Finset.range (i + 1), CB i') *
              (∑ l ∈ Finset.range (i + 1), SW l))) * W := by ring

section qCommConversion

section NormedQCommConversion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable (g₀ g₁ : SmoothRiemannianMetric I M)

omit [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] [CompactSpace M] [T2Space M]
    in
private lemma toModel_vec3_slot1_sum_smul (_x : M)
    (Zm : Tensor0SModel 3 ℝ E) (d : ℕ) (t : Fin d → ℝ) (u : Fin d → E) (a b : E) :
    Zm ![a, ∑ c, t c • u c, b] = ∑ c, t c * Zm ![a, u c, b] := by
  classical
  have h1 : ∀ v : E, (![a, v, b] : Fin 3 → E) = Function.update ![a, (0 : E), b] 1 v := by
    intro v
    funext k
    fin_cases k <;> simp [Function.update]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update ![a, (0 : E), b] 1 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update ![a, (0 : E), b] 1 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a' ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

private def sigmaQ1 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 4, 0, 3, 1, 2] : Fin 6 → Fin 6) i,
   fun i => (![2, 4, 5, 3, 1, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

private def sigmaQ2 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 2, 0, 3, 1, 4] : Fin 6 → Fin 6) i,
   fun i => (![2, 4, 1, 3, 5, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

set_option backward.isDefEq.respectTransparency false in
private lemma qCommFoldWeights_unitModel_eq_kernel (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (p q v0 v1 : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) x
        ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x p q v0 v1 := by
  classical
  have hM1 : unitModel (I := I) (M := M) g₀ 4
      (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (v0 : E)] := by
    rw [show koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 sigmaQ1
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (connDiffLoweredCc (I := I) g₀ g₁))) from rfl]
    rw [koszulConnDiffFoldWeight_unitModel_general (I := I) (M := M) g₀ g₁ sigmaQ1 P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 2))] =
        unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
          ![(q : E), (p : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![(v1 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (v0 : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, p, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hM2 : unitModel (I := I) (M := M) g₀ 4
      (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (p : E)] := by
    rw [show koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 sigmaQ2
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (connDiffLoweredCc (I := I) g₀ g₁))) from rfl]
    rw [koszulConnDiffFoldWeight_unitModel_general (I := I) (M := M) g₀ g₁ sigmaQ2 P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 2))] =
        unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
          ![(q : E), (v0 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![(v1 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (p : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, v0, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hexp : ∀ r s : TangentSpace I x,
      ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s : TangentSpace I x) : E) =
        ∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)
            (smoothOrthoFrame (I := I) g₀ x e x) •
          ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) := by
    intro r s
    rw [show (∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)
          (smoothOrthoFrame (I := I) g₀ x e x) •
        ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)) =
        ((∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)
            (smoothOrthoFrame (I := I) g₀ x e x) •
          smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) from rfl]
    conv_lhs => rw [orthoFrame_expansion_at_center (I := I) (M := M) g₀ x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)]
  have hT1 : g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) v0) v1 =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (v0 : E)] := by
    rw [← koszulCovecCc_unitModel_eq_connDiff_g1_inner (I := I) (M := M) g₀ g₁ P htie x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) v0 v1]
    conv_lhs => rw [hexp q p]
    exact toModel_vec3_slot1_sum_smul (E := E) x
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((v1 : TangentSpace I x) : E) ((v0 : TangentSpace I x) : E)
  have hT2 : g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) p) v1 =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (p : E)] := by
    rw [← koszulCovecCc_unitModel_eq_connDiff_g1_inner (I := I) (M := M) g₀ g₁ P htie x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) p v1]
    conv_lhs => rw [hexp q v0]
    exact toModel_vec3_slot1_sum_smul (E := E) x
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((v1 : TangentSpace I x) : E) ((p : TangentSpace I x) : E)
  rw [unitModel_sub_pt (I := I) (M := M) g₀ 4
    (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)
    (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) x]
  rw [ContinuousMultilinearMap.sub_apply]
  rw [hM1, hM2]
  rw [connDiffAACommKernelBilin_apply (I := I) g₀ g₁ x p q v0 v1]
  rw [hT1, hT2]

set_option backward.isDefEq.respectTransparency false in
private lemma ricciArmOrder0AACommCoeffField_eq_refold (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 2 2 x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [mvPairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
      koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁).toSection x) D) =
      connDiffAACommBiContrFib (I := I) g₀ g₁ x D from rfl]
  rw [connDiffAACommBiContrFib_toModel (I := I) g₀ g₁ x D v]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show unitModel (I := I) (M := M) g₀ 4
      (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
        koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) x
      ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] =
      connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x
        (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
        (v 0) (v 1) from
    qCommFoldWeights_unitModel_eq_kernel (I := I) (M := M) g₀ g₁ P htie x
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
      (v 0) (v 1)]

lemma exists_riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0AACommCoeffField_window
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ :=
    exists_rfns_icg_mvPairTraceOp_window (I := I) (M := M) g₀ hδ₀
  obtain ⟨CW1, hCW1_nn, hCW1⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_koszulConnDiffFoldWeight_gridWindow_le (I := I)
      (M := M) g₀ sigmaQ1 hδ₀
  obtain ⟨CW2, hCW2_nn, hCW2⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_koszulConnDiffFoldWeight_gridWindow_le (I := I)
      (M := M) g₀ sigmaQ2 hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set CX : ℕ → ℝ := fun w => fr ^ 2 * (2 * CW1 w + 2 * CW2 w) with hCX_def
  have hCX_nn : ∀ w, 0 ≤ CX w := fun w => by
    have h1 := hCW1_nn w
    have h2 := hCW2_nn w
    have h5 : (0 : ℝ) ≤ fr ^ 2 := by positivity
    simp only [hCX_def]
    nlinarith
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      ∑ u ∈ Finset.range (i + 1), CPT u *
        ∑ w ∈ Finset.range (i + 1 - u),
          CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3),
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun u _ => mul_nonneg (hCPT_nn u)
        (Finset.sum_nonneg fun w _ => mul_nonneg (hCX_nn w)
          (Combinatorics.windowPairCellCount_nonneg _ _))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  rw [ricciArmOrder0AACommCoeffField_eq_refold (I := I) (M := M) g₀ g₁ P htie]
  have hPT : ∀ u : ℕ, u ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 6 2 u
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) :=
    fun u hu => hCPT g₁ P htie hδ_le hδ0 hbound u (i + 1) (by omega) x
  have hWX : ∀ w : ℕ, w ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
                  koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)))).toSection x) ≤
        CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
    intro w hw
    rw [riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6
      ricciFoldRemainderSlotPerm _ w x]
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) =
        slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)) from rfl]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
      (slotExtend (I := I) (M := M) g₀ 0 4
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)) w x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) w x) hfr_nn) ?_
    have hsub : (iteratedCovGrad (I := I) g₀ 0 4 w
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)).toSection x -
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)).toSection x := by
      rw [sub_eq_add_neg (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)]
      rw [iteratedCovGrad_add (I := I) g₀ 0 4 w _ _,
        iteratedCovGrad_neg (I := I) g₀ 0 4 w _, SmoothCcTensor.toSection_add]
      rw [show (((iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)).toSection +
          (-(iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P))).toSection) x) =
          (iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)).toSection x +
          (-(iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P))).toSection x from rfl]
      rw [show ((-(iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P))).toSection x) =
          -((iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)).toSection x) from by
        rw [SmoothCcTensor.toSection_neg]; rfl]
      rw [← sub_eq_add_neg]
    have hA1 := hCW1 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 sigmaQ1
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P from rfl] at hA1
    have hA2 := hCW2 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 sigmaQ2
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P from rfl] at hA2
    calc fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)).toSection x))
        ≤ fr * (fr * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)).toSection x))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          rw [hsub]
          exact riemannianFiberNormSq_sub_le_pt (I := I) (M := M) g₀ 0 (4 + w) x _ _
      _ ≤ fr * (fr *
          (2 * (CW1 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
            + 2 * (CW2 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          linarith [hA1, hA2]
      _ = CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
          simp only [hCX_def]
          ring
  refine le_trans
    (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I)
    (M := M) g₀ i 2 6 2 (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P))) x) ?_
  calc diagonalGridGrowthFactor (E := E) i *
        ∑ u ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
              ((iteratedCovGrad (I := I) g₀ 6 2 u
                (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ w ∈ Finset.range (i + 1 - u),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
                ((iteratedCovGrad (I := I) g₀ 2 6 w
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
                        koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁
                          sigmaQ2 P)))).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1),
            (CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1)) *
            ∑ w ∈ Finset.range (i + 1 - u),
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u hu => ?_)
          (appCcGdiag_nonneg (E := E) i)
        rw [Finset.mem_range] at hu
        refine mul_le_mul (hPT u (by omega)) (Finset.sum_le_sum fun w hw => ?_)
          (Finset.sum_nonneg fun w _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + w) x _)
          (mul_nonneg (hCPT_nn u)
            (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))
        rw [Finset.mem_range] at hw
        exact hWX w (by omega)
    _ ≤ (diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1), CPT u *
            ∑ w ∈ Finset.range (i + 1 - u),
              CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun u hu => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun w hw => ?_
        rw [Finset.mem_range] at hu hw
        calc CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
            = (CPT u * CX w) *
                (Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)) := by ring
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 3) *
                  Combinatorics.boundedFactorGridWindow b (i + 1)
                    ((u + 1) + (w + 3) - 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn (i + 1) (u + 1)
                (w + 3) (by omega) (by omega)
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 3) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              refine mul_le_mul_of_nonneg_left ?_
                (Combinatorics.windowPairCellCount_nonneg _ _)
              exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
          _ = CPT u * (CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring

end NormedQCommConversion

end qCommConversion

section NormedAACommInputSymmetrization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


theorem rfns_iteratedCovGrad_ricciArmOrder0AACommCoeffFieldInputSymm_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSlotSymm (I := I) (M := M) g₀
                (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨Cq, hCq_nn, hCq⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0AACommCoeffField_window (I := I)
      (M := M) g₀ hδ₀
  have hSW_ex : ∀ q : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 2 q
          (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) ≤ c := fun q =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + q)
      (iteratedCovGrad (I := I) g₀ 2 2 q (ccInputSlotSwapField (I := I) (M := M) g₀))
  choose SW hSW_nn hSW using hSW_ex
  refine ⟨fun i => (1 / 2 : ℝ) * Cq i +
      (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), Cq i') *
        (∑ l ∈ Finset.range (i + 1), SW l)), ?_, ?_⟩
  · intro i
    have h2 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), Cq i' := Finset.sum_nonneg fun i' _ => hCq_nn i'
    have h3 : 0 ≤ ∑ l ∈ Finset.range (i + 1), SW l := Finset.sum_nonneg fun l _ => hSW_nn l
    have h4 : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
    have h1 : 0 ≤ Cq i := hCq_nn i
    positivity
  · intro g₁ P htie δ hδ_le hδ0 hbound i x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
    have hb_nn : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set W : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hW_def
    have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
    have hQ : ∀ n : ℕ, n ≤ i →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x) ≤
        Cq n * W := by
      intro n hn
      refine le_trans (hCq g₁ P htie hδ_le hδ0 hbound n x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCq_nn n)
      rw [hW_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (by omega)
    have hsubject : ccInputSlotSymm (I := I) (M := M) g₀
        (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁) =
        (1 / 2 : ℝ) • (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀)) := rfl
    rw [hsubject]
    have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
        ((1 / 2 : ℝ) • (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀)))).toSection x =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
              (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
              (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) := by
      rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
        SmoothCcTensor.toSection_smul]
      rfl
    rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
      show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
    have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
              (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
              (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
      rfl
    rw [hsplit]
    refine le_trans (mul_le_mul_of_nonneg_left
      (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
    have hQi : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x) ≤
        Cq i * W :=
      hQ i (le_refl i)
    have hApp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
        diagonalGridGrowthFactor (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Cq i') *
          ((∑ l ∈ Finset.range (i + 1), SW l) * W)) := by
      refine le_trans
        (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
        (I := I) (M := M) g₀ i 2 2 2
        (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
        (ccInputSlotSwapField (I := I) (M := M) g₀) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i' hi' => ?_
      rw [Finset.mem_range] at hi'
      have hswapsum : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1), SW l := by
        refine le_trans (Finset.sum_le_sum fun l _ => hSW l x) ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega)) ?_
        exact fun l _ _ => hSW_nn l
      have hQi' := hQ i' (by omega)
      have hswap_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 2 2 i'
                (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l
                  (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)
          ≤ (Cq i' * W) * (∑ l ∈ Finset.range (i + 1), SW l) :=
            mul_le_mul hQi' hswapsum hswap_nn (mul_nonneg (hCq_nn i') hW_nn)
        _ = Cq i' * ((∑ l ∈ Finset.range (i + 1), SW l) * W) := by ring
    calc (1 / 4 : ℝ) * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
                (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
                (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x))
        ≤ (1 / 4 : ℝ) * (2 * (Cq i * W)
            + 2 * (diagonalGridGrowthFactor (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Cq i') *
              ((∑ l ∈ Finset.range (i + 1), SW l) * W)))) := by
          nlinarith [hQi, hApp]
      _ = ((1 / 2 : ℝ) * Cq i +
            (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i *
              (∑ i' ∈ Finset.range (i + 1), Cq i') *
              (∑ l ∈ Finset.range (i + 1), SW l))) * W := by ring

end NormedAACommInputSymmetrization

set_option backward.isDefEq.respectTransparency false

open DifferentialGeometry.Integral.DivergenceTheorem

omit [BoundarylessManifold I M] in
theorem refoldKernelContractionMonomialField_eq_mvPairTraceRefold
    (g₀ g₁ : SmoothRiemannianMetric I M) (G : SmoothCcTensor g₀ 0 4)
    (σ : Equiv.Perm (Fin 4)) :
    refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (domDomCongrSection (I := I) g₀
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ) G))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  refine tensorRSSpace_ext 2 2 x (fun D => ?_)
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [mvPairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    (domDomCongrSection (I := I) g₀
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ) G) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ).toSection x) D) =
      curvatureRefoldMonomialOrthonormalFrameBiContraction (I := I) (M := M) g₁
        (ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀ G) σ x D from rfl]
  rw [curvatureRefoldMonomialOrthonormalFrameBiContraction,
    refoldKernelContractionMonomialFibFixedFrame_toModel]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine congrArg₂ (· * ·) rfl ?_
  rw [domDomCongrSection_unitModel (I := I) g₀
    (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ) G x,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [show unitModel (I := I) (M := M) g₀ 4 G x =
      Tensor0SSpace.toModel (𝕜 := ℝ)
        (ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀ G x) from rfl]
  refine congrArg _ ?_
  funext j
  rw [show ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ) j) =
      ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) (σ j)) from rfl]
  have hcons : ∀ k : Fin 4,
      (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E) v) :
          Fin 4 → E) k =
      (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → E)
        ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) k) := by
    intro k
    fin_cases k <;>
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> rfl
  exact hcons (σ j)

private theorem exists_rfns_icg_refoldKernelContractionMonomialField_window
    (g₀ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 4)) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
                σ)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ :=
    exists_rfns_icg_mvPairTraceOp_window (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      ∑ n ∈ Finset.range (i + 1), CPT n * ∑ l ∈ Finset.range (i + 1 - n), fr ^ 2,
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun n _ => mul_nonneg (hCPT_nn n)
        (Finset.sum_nonneg fun l _ => by positivity)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  rw [refoldKernelContractionMonomialField_eq_mvPairTraceRefold (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) σ]
  refine le_trans
    (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ i 2 6 2 (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))))) x) ?_
  have hPT : ∀ n : ℕ, n ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 6 2 n
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CPT n * Combinatorics.boundedFactorGridWindow b (i + 2) (n + 1) :=
    fun n hn => hCPT g₁ P htie hδ_le hδ0 hbound n (i + 2) (by omega) x
  have hWb : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (domDomCongrSection (I := I) g₀
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                  (iteratedCovGrad (I := I) g₀ 0 2 2
                    (ccTensor02Symm (I := I) (M := M) g₀ P)))))).toSection x) ≤
        fr ^ 2 * b (2 + l) := by
    intro l
    rw [riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6
      ricciFoldRemainderSlotPerm _ l x]
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))) =
        slotExtend (I := I) (M := M) g₀ 1 5
          (slotExtend (I := I) (M := M) g₀ 0 4
            (domDomCongrSection (I := I) g₀
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))))
        from rfl]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5 _ l x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4 _ l x) hfr_nn) ?_
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
      (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) l x]
    rw [riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 2 l
      (ccTensor02Symm (I := I) (M := M) g₀ P) x]
    have hsymm := rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ P (2 + l) x
    have hstep : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + l)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (2 + l)
          (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x) ≤ b (2 + l) := hsymm
    calc fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + l)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (2 + l)
              (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x))
        ≤ fr * (fr * b (2 + l)) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hstep hfr_nn) hfr_nn
      _ = fr ^ 2 * b (2 + l) := by ring
  have hterm : ∀ n ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 6 2 n
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - n),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                    (iteratedCovGrad (I := I) g₀ 0 2 2
                      (ccTensor02Symm (I := I) (M := M) g₀ P)))))).toSection x) ≤
      (CPT n * ∑ l ∈ Finset.range (i + 1 - n), fr ^ 2) *
        Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hn' : n ≤ i := by omega
    have hsumW : (∑ l ∈ Finset.range (i + 1 - n),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (domDomCongrSection (I := I) g₀
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                  (iteratedCovGrad (I := I) g₀ 0 2 2
                    (ccTensor02Symm (I := I) (M := M) g₀ P)))))).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - n), fr ^ 2 * b (2 + l) :=
      Finset.sum_le_sum (fun l _ => hWb l)
    have hW_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - n),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (domDomCongrSection (I := I) g₀
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                  (iteratedCovGrad (I := I) g₀ 0 2 2
                    (ccTensor02Symm (I := I) (M := M) g₀ P)))))).toSection x) :=
      Finset.sum_nonneg (fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _)
    refine le_trans (mul_le_mul (hPT n hn') hsumW hW_nn
      (mul_nonneg (hCPT_nn n)
        (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))) ?_
    rw [Finset.mul_sum]
    rw [show (CPT n * ∑ l ∈ Finset.range (i + 1 - n), fr ^ 2) *
        Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) =
        ∑ l ∈ Finset.range (i + 1 - n),
          CPT n * fr ^ 2 * Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum (fun l hl => ?_)
    rw [Finset.mem_range] at hl
    have habsorb : b (2 + l) * Combinatorics.boundedFactorGridWindow b (i + 2) (n + 1) ≤
        Combinatorics.boundedFactorGridWindow b (i + 2) ((n + 1) + (2 + l)) :=
      Combinatorics.single_factor_mul_boundedFactorGridWindow_le b hb_nn
        (by omega) (by omega)
    have hmono : Combinatorics.boundedFactorGridWindow b (i + 2) ((n + 1) + (2 + l)) ≤
        Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) :=
      Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
    calc CPT n * Combinatorics.boundedFactorGridWindow b (i + 2) (n + 1) *
            (fr ^ 2 * b (2 + l))
        = (CPT n * fr ^ 2) *
            (b (2 + l) * Combinatorics.boundedFactorGridWindow b (i + 2) (n + 1)) := by
          ring
      _ ≤ (CPT n * fr ^ 2) *
            Combinatorics.boundedFactorGridWindow b (i + 2) ((n + 1) + (2 + l)) :=
          mul_le_mul_of_nonneg_left habsorb
            (mul_nonneg (hCPT_nn n) (by positivity))
      _ ≤ (CPT n * fr ^ 2) *
            Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) :=
          mul_le_mul_of_nonneg_left hmono
            (mul_nonneg (hCPT_nn n) (by positivity))
      _ = CPT n * fr ^ 2 * Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) := by
          ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [← Finset.sum_mul]
  exact le_of_eq (by ring)

private lemma quarter_four_term_bound
    {z z123 z12 z1 z2 z3 z4 c1 c2 c3 c4 w : ℝ}
    (h1 : z1 ≤ c1 * w) (h2 : z2 ≤ c2 * w)
    (h3 : z3 ≤ c3 * w) (h4 : z4 ≤ c4 * w)
    (hs1 : z ≤ 2 * z123 + 2 * z4)
    (hs2 : z123 ≤ 2 * z12 + 2 * z3)
    (hs3 : z12 ≤ 2 * z1 + 2 * z2)
    (hw : 0 ≤ w) (hc4 : 0 ≤ c4) :
    (1 / 4 : ℝ) * z ≤ (2 * c1 + 2 * c2 + c3 + c4) * w := by
  nlinarith

private theorem exists_rfns_icg_refoldKernelContractionField_window
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (refoldKernelContractionField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
                (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
                (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3) := by
  classical
  obtain ⟨C1, hC1_nn, hC1⟩ :=
    exists_rfns_icg_refoldKernelContractionMonomialField_window (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 2) hδ₀
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_rfns_icg_refoldKernelContractionMonomialField_window (I := I) (M := M) g₀
      (Equiv.swap (1 : Fin 4) 3) hδ₀
  obtain ⟨C3, hC3_nn, hC3⟩ :=
    exists_rfns_icg_refoldKernelContractionMonomialField_window (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) hδ₀
  obtain ⟨C4, hC4_nn, hC4⟩ :=
    exists_rfns_icg_refoldKernelContractionMonomialField_window (I := I) (M := M) g₀
      (1 : Equiv.Perm (Fin 4)) hδ₀
  refine ⟨fun i => 2 * C1 i + 2 * C2 i + C3 i + C4 i,
    fun i => by
      have := hC1_nn i; have := hC2_nn i; have := hC3_nn i; have := hC4_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set G : SmoothCcTensor g₀ 0 4 :=
    iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P) with hG_def
  set m1 := refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G
    (Equiv.swap (0 : Fin 4) 2) with hm1_def
  set m2 := refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G
    (Equiv.swap (1 : Fin 4) 3) with hm2_def
  set m3 := refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G
    (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) with hm3_def
  set m4 := refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G
    (1 : Equiv.Perm (Fin 4)) with hm4_def
  have hker : refoldKernelContractionField (I := I) (M := M) g₀ g₁ G
      (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 =
      (1 / 2 : ℝ) • (m1 + m2 - m3 - m4) := rfl
  have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
      ((1 / 2 : ℝ) • (m1 + m2 - m3 - m4))).toSection x =
      (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (m1 + m2 - m3 - m4)).toSection x) := by
    rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
      SmoothCcTensor.toSection_smul]
    rfl
  have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 i (m1 + m2 - m3 - m4)).toSection x =
      ((iteratedCovGrad (I := I) g₀ 2 2 i m1).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i m2).toSection x
        - (iteratedCovGrad (I := I) g₀ 2 2 i m3).toSection x)
        - (iteratedCovGrad (I := I) g₀ 2 2 i m4).toSection x := by
    rw [show m1 + m2 - m3 - m4 = (m1 + m2 - m3) - m4 from rfl, iteratedCovGrad_sub,
      show m1 + m2 - m3 = (m1 + m2) - m3 from rfl, iteratedCovGrad_sub, iteratedCovGrad_add]
    rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub,
      SmoothCcTensor.toSection_add]
    rfl
  rw [hker, hsm, hsplit]
  rw [riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
    show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
  have h1 := hC1 g₁ P htie hδ_le hδ0 hbound i x
  have h2 := hC2 g₁ P htie hδ_le hδ0 hbound i x
  have h3 := hC3 g₁ P htie hδ_le hδ0 hbound i x
  have h4 := hC4 g₁ P htie hδ_le hδ0 hbound i x
  have hs1 := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x
    ((iteratedCovGrad (I := I) g₀ 2 2 i m1).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 2 i m2).toSection x
      - (iteratedCovGrad (I := I) g₀ 2 2 i m3).toSection x)
    ((iteratedCovGrad (I := I) g₀ 2 2 i m4).toSection x)
  have hs2 := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x
    ((iteratedCovGrad (I := I) g₀ 2 2 i m1).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 2 i m2).toSection x)
    ((iteratedCovGrad (I := I) g₀ 2 2 i m3).toSection x)
  have hs3 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x
    ((iteratedCovGrad (I := I) g₀ 2 2 i m1).toSection x)
    ((iteratedCovGrad (I := I) g₀ 2 2 i m2).toSection x)
  have hgrid_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) :=
    Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
  exact quarter_four_term_bound h1 h2 h3 h4 hs1 hs2 hs3 hgrid_nn (hC4_nn i)


theorem rfns_iteratedCovGrad_refoldKernelContractionFieldInputSymm_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSlotSymm (I := I) (M := M) g₀
                (refoldKernelContractionField (I := I) (M := M) g₀ g₁
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
                  (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1))).toSection
              x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3) := by
  classical
  obtain ⟨Ck, hCk_nn, hCk⟩ :=
    exists_rfns_icg_refoldKernelContractionField_window (I := I) (M := M) g₀ hδ₀
  have hSW_ex : ∀ q : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 2 q
          (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) ≤ c := fun q =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + q)
      (iteratedCovGrad (I := I) g₀ 2 2 q (ccInputSlotSwapField (I := I) (M := M) g₀))
  choose SW hSW_nn hSW using hSW_ex
  refine ⟨fun i => (1 / 2 : ℝ) * Ck i +
      (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), Ck i') *
        (∑ l ∈ Finset.range (i + 1), SW l)), ?_, ?_⟩
  · intro i
    have h2 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), Ck i' :=
      Finset.sum_nonneg fun i' _ => hCk_nn i'
    have h3 : 0 ≤ ∑ l ∈ Finset.range (i + 1), SW l :=
      Finset.sum_nonneg fun l _ => hSW_nn l
    have h4 : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
    have h1 : 0 ≤ Ck i := hCk_nn i
    positivity
  · intro g₁ P htie δ hδ_le hδ0 hbound i x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
    have hb_nn : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set W : ℝ := Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) with hW_def
    have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
    set K : SmoothCcTensor g₀ 2 2 :=
      refoldKernelContractionField (I := I) (M := M) g₀ g₁
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
        (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
        (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 with hK_def
    have hQ : ∀ n : ℕ, n ≤ i →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n K).toSection x) ≤ Ck n * W := by
      intro n hn
      refine le_trans (hCk g₁ P htie hδ_le hδ0 hbound n x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCk_nn n)
      rw [hW_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (by omega)
    have hsubject : ccInputSlotSymm (I := I) (M := M) g₀ K =
        (1 / 2 : ℝ) • (K + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 K
          (ccInputSlotSwapField (I := I) (M := M) g₀)) := rfl
    rw [hsubject]
    have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
        ((1 / 2 : ℝ) • (K + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 K
          (ccInputSlotSwapField (I := I) (M := M) g₀)))).toSection x =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (K + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 K
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) := by
      rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
        SmoothCcTensor.toSection_smul]
      rfl
    rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
      show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
    have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 i
        (K + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 K
          (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i K).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 K
              (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
      rfl
    rw [hsplit]
    refine le_trans (mul_le_mul_of_nonneg_left
      (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
    have hQi : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i K).toSection x) ≤ Ck i * W :=
      hQ i (le_refl i)
    have hApp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 K
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
        diagonalGridGrowthFactor (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Ck i') *
          ((∑ l ∈ Finset.range (i + 1), SW l) * W)) := by
      refine le_trans
        (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
        (I := I) (M := M) g₀ i 2 2 2 K (ccInputSlotSwapField (I := I) (M := M) g₀) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i' hi' => ?_
      rw [Finset.mem_range] at hi'
      have hswapsum : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1), SW l := by
        refine le_trans (Finset.sum_le_sum fun l _ => hSW l x) ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega)) ?_
        exact fun l _ _ => hSW_nn l
      have hQi' := hQ i' (by omega)
      have hswap_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 2 2 i' K).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l
                  (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)
          ≤ (Ck i' * W) * (∑ l ∈ Finset.range (i + 1), SW l) :=
            mul_le_mul hQi' hswapsum hswap_nn (mul_nonneg (hCk_nn i') hW_nn)
        _ = Ck i' * ((∑ l ∈ Finset.range (i + 1), SW l) * W) := by ring
    calc (1 / 4 : ℝ) * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i K).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 K
                (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x))
        ≤ (1 / 4 : ℝ) * (2 * (Ck i * W)
            + 2 * (diagonalGridGrowthFactor (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Ck i') *
              ((∑ l ∈ Finset.range (i + 1), SW l) * W)))) := by
          nlinarith [hQi, hApp]
      _ = ((1 / 2 : ℝ) * Ck i +
            (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i *
              (∑ i' ∈ Finset.range (i + 1), Ck i') *
              (∑ l ∈ Finset.range (i + 1), SW l))) * W := by ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
