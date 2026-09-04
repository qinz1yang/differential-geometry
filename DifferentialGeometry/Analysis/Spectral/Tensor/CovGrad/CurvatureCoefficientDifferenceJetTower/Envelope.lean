import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Grid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Palatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.PairTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.TraceGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.ReindexingNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ConnectionBicontraction
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.MetricComparisonEndomorphismJetBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricDoubleTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.RecoveryEndomorphismJetBounds
import DifferentialGeometry.Tensor.Multilinear.Bundle.Basis
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNorm.UniformBound
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Algebra
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenberg.FiberNorm.Basic
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.HigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.JetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.RaisedKoszul.JetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.RaisedKoszul.ParallelRaiseJetBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.CovariantOrderFibreNormBounds
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifference.RicciPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.ApplicationJets
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.Connection

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (gFibreOpBound metricCauchySchwarzBound ccTensorBilinSymm smoothCcTensorBilinForm ccTensorBilin_apply
  ccTensorModel ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply
  ccTensorBilinSymm_symm)
open DifferentialGeometry.PDE.RicciFlow
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

theorem riemannianFiberNormSq_iteratedCovGrad_riemannCoeff_metricFactorTelescope_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciOrderZeroRiemannMixedCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CC, hCC_nn, hCC⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannCoeff_metricFactorTelescope_traceConversion_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨C1, hC1_nn, hC1⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannG1LoweringDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_backgroundJet_riemannianFiberNormSq_bound (I := I) (M := M) g₀ 0 4
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)
  refine ⟨fun i => CC i * ∑ j ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (i + 1),
      (2 * cbg l + (2 * CA l + C1 l) * CurvatureCoefficientDifferenceJetTower.tWindowMulConst l j),
    fun i => mul_nonneg (hCC_nn i) (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ =>
      add_nonneg (by have := hcbg_nn l; linarith)
        (mul_nonneg (by have := hCA_nn l; have := hC1_nn l; linarith)
          (tWindowMulConst_nonneg l j))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hP : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) ≤
      2 * cbg l + 2 * CA l * CurvatureCoefficientDifferenceJetTower.tWindow b l := by
    intro l
    have hsplit : riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ =
        riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ +
          riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀ := by
      rw [riemannLoweredBackgroundDifference, sub_add_cancel]
    have hsec : (iteratedCovGrad (I := I) g₀ 0 4 l
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x := by
      rw [hsplit, iteratedCovGrad_add, SmoothCcTensor.toSection_add]
      rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + l) x _ _) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CA l * CurvatureCoefficientDifferenceJetTower.tWindow b l := by
      have h := hCA g₁ T htie hδ_le hδ0 hbound l x
      rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x l] at h
      exact h
    have h2 := hcbg l x
    linarith
  have hQ : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
            riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) ≤
      C1 l * CurvatureCoefficientDifferenceJetTower.tWindow b l := by
    intro l
    have h := hC1 g₁ T htie hδ_le hδ0 hbound l x
    rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x l] at h
    exact h
  refine le_trans (hCC g₁ T htie hδ_le hδ0 hbound i x) ?_
  rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
  have hjl : ∀ j ∈ Finset.range (i + 1),
      (∑ n ∈ Finset.range (j + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          ∏ m : Fin n, b (e m)) *
        (∑ l ∈ Finset.range (i + 1 - j),
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                  riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x))) ≤
      (∑ l ∈ Finset.range (i + 1),
        (2 * cbg l + (2 * CA l + C1 l) * CurvatureCoefficientDifferenceJetTower.tWindowMulConst l j)) * CurvatureCoefficientDifferenceJetTower.tWindow b i := by
    intro j hj
    have hjle : j ≤ i := by
      have := Finset.mem_range.mp hj
      omega
    have hgrid_eq : (∑ n ∈ Finset.range (j + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n j, ∏ m : Fin n, b (e m)) =
        Combinatorics.antidiagonalTupleGrid b j := rfl
    rw [hgrid_eq, mul_comm (Combinatorics.antidiagonalTupleGrid b j)]
    rw [Finset.sum_mul]
    have hterm : ∀ l ∈ Finset.range (i + 1 - j),
        (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)) *
          Combinatorics.antidiagonalTupleGrid b j ≤
        (2 * cbg l + (2 * CA l + C1 l) * CurvatureCoefficientDifferenceJetTower.tWindowMulConst l j) * CurvatureCoefficientDifferenceJetTower.tWindow b i := by
      intro l hl
      have hlle : l ≤ i - j := by
        have := Finset.mem_range.mp hl
        omega
      have hlj : l + j ≤ i := by omega
      have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b j :=
        Combinatorics.antidiagonalTupleGrid_nonneg b hb j
      have hgrid_le : Combinatorics.antidiagonalTupleGrid b j ≤ CurvatureCoefficientDifferenceJetTower.tWindow b i :=
        antidiagonalTupleGrid_le_tWindow b hb (by omega)
      have hsum_le : (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)) ≤
          2 * cbg l + (2 * CA l + C1 l) * CurvatureCoefficientDifferenceJetTower.tWindow b l := by
        have h1 := hP l
        have h2 := hQ l
        have hW_nn : 0 ≤ CurvatureCoefficientDifferenceJetTower.tWindow b l := tWindow_nonneg b hb l
        nlinarith [hCA_nn l, hC1_nn l]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                  riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)) *
            Combinatorics.antidiagonalTupleGrid b j
          ≤ (2 * cbg l + (2 * CA l + C1 l) * CurvatureCoefficientDifferenceJetTower.tWindow b l) *
              Combinatorics.antidiagonalTupleGrid b j :=
            mul_le_mul_of_nonneg_right hsum_le hgrid_nn
        _ = 2 * cbg l * Combinatorics.antidiagonalTupleGrid b j +
              (2 * CA l + C1 l) * (CurvatureCoefficientDifferenceJetTower.tWindow b l * Combinatorics.antidiagonalTupleGrid b j) := by
            ring
        _ ≤ 2 * cbg l * CurvatureCoefficientDifferenceJetTower.tWindow b i +
              (2 * CA l + C1 l) * (CurvatureCoefficientDifferenceJetTower.tWindowMulConst l j * CurvatureCoefficientDifferenceJetTower.tWindow b (l + j)) := by
            have hmul := tWindow_mul_antidiagonalTupleGrid_le b hb l j
            have hnn1 : 0 ≤ 2 * cbg l := by have := hcbg_nn l; linarith
            have hnn2 : 0 ≤ 2 * CA l + C1 l := by
              have := hCA_nn l; have := hC1_nn l; linarith
            exact add_le_add (mul_le_mul_of_nonneg_left hgrid_le hnn1)
              (mul_le_mul_of_nonneg_left hmul hnn2)
        _ ≤ 2 * cbg l * CurvatureCoefficientDifferenceJetTower.tWindow b i +
              (2 * CA l + C1 l) * (CurvatureCoefficientDifferenceJetTower.tWindowMulConst l j * CurvatureCoefficientDifferenceJetTower.tWindow b i) := by
            have hnn2 : 0 ≤ 2 * CA l + C1 l := by
              have := hCA_nn l; have := hC1_nn l; linarith
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (tWindow_mono b hb hlj)
                (tWindowMulConst_nonneg l j)) hnn2)
        _ = (2 * cbg l + (2 * CA l + C1 l) * CurvatureCoefficientDifferenceJetTower.tWindowMulConst l j) * CurvatureCoefficientDifferenceJetTower.tWindow b i := by
            ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (tWindow_nonneg b hb i)
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) ?_
    intro l _ _
    exact add_nonneg (by have := hcbg_nn l; linarith)
      (mul_nonneg (by have := hCA_nn l; have := hC1_nn l; linarith)
        (tWindowMulConst_nonneg l j))
  calc CC i * ∑ j ∈ Finset.range (i + 1),
        (∑ n ∈ Finset.range (j + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
            ∏ m : Fin n, b (e m)) *
          ∑ l ∈ Finset.range (i + 1 - j),
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                    riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x))
      ≤ CC i * ∑ j ∈ Finset.range (i + 1),
          (∑ l ∈ Finset.range (i + 1),
            (2 * cbg l + (2 * CA l + C1 l) * CurvatureCoefficientDifferenceJetTower.tWindowMulConst l j)) * CurvatureCoefficientDifferenceJetTower.tWindow b i :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hjl) (hCC_nn i)
    _ = CC i * (∑ j ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (i + 1),
          (2 * cbg l + (2 * CA l + C1 l) * CurvatureCoefficientDifferenceJetTower.tWindowMulConst l j)) * CurvatureCoefficientDifferenceJetTower.tWindow b i := by
        rw [← Finset.sum_mul]
        ring

theorem riemannianFiberNormSq_iteratedCovGrad_ricciOrderZeroRiemannCoeff_backgroundDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨Ca, hCa_nn, hCa⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannCoeff_metricFactorTelescope_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  refine ⟨fun i => 2 * Cb i + 2 * Ca i,
    fun i => by have := hCa_nn i; have := hCb_nn i; linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  have hb : ∀ j : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
  have hsplit : ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ =
      (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciOrderZeroRiemannMixedCoeff (I := I) (M := M) g₀ g₁) +
      (ricciOrderZeroRiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
        ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀) := by
    rw [sub_add_sub_cancel]
  have hsec : (iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x =
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciOrderZeroRiemannMixedCoeff (I := I) (M := M) g₀ g₁)).toSection x +
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciOrderZeroRiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
            ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x := by
    rw [hsplit, iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
  have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciOrderZeroRiemannMixedCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
      Cb i * CurvatureCoefficientDifferenceJetTower.tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
    rw [tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
    exact hCb g₁ T htie hδ_le hδ0 hbound i x
  have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
          ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
      Ca i * CurvatureCoefficientDifferenceJetTower.tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
    rw [tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
    exact hCa g₁ T htie hδ_le hδ0 hbound i x
  rw [show (2 * Cb i + 2 * Ca i) *
      CurvatureCoefficientDifferenceJetTower.tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i =
      2 * (Cb i * CurvatureCoefficientDifferenceJetTower.tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i) +
        2 * (Ca i * CurvatureCoefficientDifferenceJetTower.tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i) from by ring]
  linarith

theorem slotInsertEndoCc_ricEndoBackgroundDifferenceField_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ ^ 2 ≤ K i := by
  obtain ⟨C, hC_nn, hgrid⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    curvDiffGrid_integral_ballUniform_window (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
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
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hkle : ∀ k ∈ Finset.range (i + 3), k ≤ a + 2 := by
      intro k hk
      rw [Finset.mem_range] at hk
      omega
    have hF_int : MeasureTheory.Integrable
        (fun x => C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (MeasureTheory.integrable_finsetSum _
        (fun k hk => (hKg P hPball k (hkle k hk)).1)).const_mul (C i)
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      hF_int
      (fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finsetSum _ (fun k hk => (hKg P hPball k (hkle k hk)).1)]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun k hk => (hKg P hPball k (hkle k hk)).2)) (hC_nn i)
  · have hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    simpa using mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k))

theorem ricciOrderZeroRiemannCoeff_backgroundDifference_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ K i := by
  obtain ⟨C, hC_nn, hgrid⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciOrderZeroRiemannCoeff_backgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    curvDiffGrid_integral_ballUniform_window (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
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
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hkle : ∀ k ∈ Finset.range (i + 3), k ≤ a + 2 := by
      intro k hk
      rw [Finset.mem_range] at hk
      omega
    have hF_int : MeasureTheory.Integrable
        (fun x => C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (MeasureTheory.integrable_finsetSum _
        (fun k hk => (hKg P hPball k (hkle k hk)).1)).const_mul (C i)
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀))
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      hF_int
      (fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finsetSum _ (fun k hk => (hKg P hPball k (hkle k hk)).1)]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun k hk => (hKg P hPball k (hkle k hk)).2)) (hC_nn i)
  · have hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    simpa using mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k))

theorem ricciOrderZeroCurvCoeff_backgroundDifference_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ K i := by
  obtain ⟨K, hK_nn, hK⟩ :=
    slotInsertEndoCc_ricEndoBackgroundDifferenceField_perOrder_l2_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 4 * (Module.finrank ℝ E : ℝ) * K i,
    fun i => mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (hK_nn i), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  have hKi := hK g₁ P hδ_le hδ htie hPball i hi
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
        4 * (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) := by
    intro x
    have hsec : (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁ -
            ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x +
          (iteratedCovGrad (I := I) g₀ 2 2 i
            (reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
              (Equiv.swap (0 : Fin 2) 1))).toSection x := by
      rw [ricciOrderZeroCurvCoeff_backgroundDifference_decomp (I := I) (M := M) g₀ g₁,
        iteratedCovGrad_add (I := I) g₀ 2 2 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))
          (reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
            (Equiv.swap (0 : Fin 2) 1)),
        SmoothCcTensor.toSection_add]
      rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
    have hswap : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
            (Equiv.swap (0 : Fin 2) 1))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 2
        (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)) i x
    rw [hswap]
    have hendo : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) := by
      have h := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) i x
      rw [pow_one] at h
      exact h
    linarith [hendo]
  have hF_int : MeasureTheory.Integrable
      (fun x => 4 * (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁ -
        ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀))
    (fun x => 4 * (Module.finrank ℝ E : ℝ) *
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
    hF_int hpt
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 1 (1 + i)
    (iteratedCovGrad (I := I) g₀ 1 1 i
      (slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))]
  rw [← SmoothCcTensor.norm_def]
  exact mul_le_mul_of_nonneg_left hKi (by positivity)

theorem antidiagonalTupleGrid_integral_ballUniform_tameWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (i + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, ∑ n ∈ Finset.range (i + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.Analysis.Spectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Lam : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R with hLam
  have hLam_nn : 0 ≤ Lam := by rw [hLam]; positivity
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose_spec.1
    · exact le_refl 0
  set Gfun : ℕ → ℝ := fun k => (k : ℝ) * (max Lam (max (Cgn k) 1)) ^ (7 * k) with hGfun
  have hGfun_nn : ∀ k, 0 ≤ Gfun k := by
    intro k
    rw [hGfun]
    apply mul_nonneg (Nat.cast_nonneg k)
    apply pow_nonneg
    exact le_trans zero_le_one
      (le_trans (le_max_right (Cgn k) 1) (le_max_right Lam _))
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal with hvol
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hK_nn : ∀ k, 0 ≤ (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * Gfun k + vol := by
    intro k
    exact add_nonneg
      (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn k)) hvol_nn
  refine ⟨fun k => (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * Gfun k + vol, hK_nn, ?_⟩
  intro P hPball i
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hone_le : (1 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by linarith
  by_cases hi0 : i = 0
  · subst hi0
    have hgrid0 : (fun x => ∑ n ∈ Finset.range (0 + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = (fun _ : M => (1 : ℝ)) := by
      funext x
      simp only [Nat.zero_add, Finset.sum_range_one, Finset.Nat.antidiagonalTuple_zero_zero,
        Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]
    refine ⟨?_, ?_⟩
    · rw [hgrid0]; exact MeasureTheory.integrable_const 1
    · rw [hgrid0, MeasureTheory.integral_const, smul_eq_mul, mul_one,
        MeasureTheory.measureReal_def, ← hvol]
      calc vol ≤ ((∑ n ∈ Finset.range (0 + 1),
              ((Finset.Nat.antidiagonalTuple n 0).card : ℝ)) * Gfun 0 + vol) * 1 := by
            rw [mul_one]
            exact le_add_of_nonneg_left
              (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn 0))
        _ ≤ ((∑ n ∈ Finset.range (0 + 1),
              ((Finset.Nat.antidiagonalTuple n 0).card : ℝ)) * Gfun 0 + vol) *
            (1 + ∑ j ∈ Finset.range (0 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hone_le (hK_nn 0)
  · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
    have hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
        Lam ^ 2 := by
      intro x
      have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
        calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
            ≤ ∑ j ∈ Finset.range (a + 1 + 1), R ^ 2 := by
              apply Finset.sum_le_sum
              intro j hj
              have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
              nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hPball j hjle, hR]
          _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
          ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) := by
        have h0mem : (0 : ℕ) ∈ Finset.range 3 := by norm_num
        have hsl := Finset.single_le_sum
          (f := fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x))
          (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _) h0mem
        simpa using hsl
      have hLam2 : Lam ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
        rw [hLam, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      have hchain : ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2 := by
        refine le_trans (hCemb P x) ?_
        rw [hLam2]
        calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
            ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
              mul_le_mul_of_nonneg_left hsum_le (by positivity)
          _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring
      exact le_trans hsingle hchain
    have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
      (I := I) (M := M) g₀ 0 2 i hi1).choose_spec.2
    have hGNP : ∀ j : ℕ, 0 < j → j < i →
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
          Cgn i * Lam ^ (2 * (1 - (j : ℝ) / (i : ℝ))) *
            ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ (2 * (j : ℝ) / (i : ℝ)) := by
      intro j hj0 hji
      have hb := hGNspec P Lam hLam_nn hΛsup j hj0 hji
      have hchoose : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g₀ 0 2 i hi1).choose = Cgn i := by
        rw [hCgn]; simp only [dif_pos hi1]
      rw [hchoose] at hb
      have hnorm : Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
          (iteratedCovGrad (I := I) g₀ 0 2 i P).toFun = ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ :=
        (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P)).symm
      rw [hnorm] at hb
      exact hb
    have hPT : ∀ n ∈ Finset.range (i + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n i,
        MeasureTheory.Integrable (fun x => ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
        (∫ x, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          Gfun i * ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
      intro n hn e he
      have hn_le : n ≤ i := by have := Finset.mem_range.mp hn; omega
      have hsum_e : ∑ m, e m = i := Finset.Nat.mem_antidiagonalTuple.mp he
      have hres := grid_prod_int_le (I := I) (M := M) g₀ P
        (norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i P)) i hi1 hLam_nn hΛsup
        (le_refl _) (hCgn_nn i) hGNP n hn_le e hsum_e
      refine ⟨hres.1, ?_⟩
      refine le_trans hres.2 (le_of_eq ?_)
      simp only [hGfun]
    have hgrid_int : MeasureTheory.Integrable (fun x => ∑ n ∈ Finset.range (i + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      apply MeasureTheory.integrable_finsetSum
      intro n hn
      apply MeasureTheory.integrable_finsetSum
      intro e he
      exact (hPT n hn e he).1
    refine ⟨hgrid_int, ?_⟩
    rw [MeasureTheory.integral_finsetSum _
      (fun n hn => MeasureTheory.integrable_finsetSum _ (fun e he => (hPT n hn e he).1))]
    have hinner : ∀ n ∈ Finset.range (i + 1),
        (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
        ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      intro n hn
      exact MeasureTheory.integral_finsetSum _ (fun e he => (hPT n hn e he).1)
    rw [Finset.sum_congr rfl hinner]
    have hle1 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          Gfun i * ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
      apply Finset.sum_le_sum; intro n hn
      apply Finset.sum_le_sum; intro e he
      exact (hPT n hn e he).2
    have heq2 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          Gfun i * ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 =
        (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
          (Gfun i * ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro n _
      rw [Finset.sum_const, nsmul_eq_mul]
    refine le_trans hle1 ?_
    rw [heq2]
    have htop_le : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 ≤
        1 + ∑ j ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      have hmem : i ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
      have := Finset.single_le_sum
        (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
        (fun j _ => sq_nonneg _) hmem
      linarith
    have hcard_nn : 0 ≤ ∑ n ∈ Finset.range (i + 1),
        ((Finset.Nat.antidiagonalTuple n i).card : ℝ) :=
      Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)
    calc (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            (Gfun i * ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2)
        ≤ (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            (Gfun i * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hcard_nn
          exact mul_le_mul_of_nonneg_left htop_le (hGfun_nn i)
      _ = ((∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            Gfun i) * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
      _ ≤ ((∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            Gfun i + vol) * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          linarith

namespace CurvatureCoefficientDifferenceJetTower

lemma tame_sq_le_two_add (t u v c1 c2 : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htri : t ≤ u + v) (h1 : u ^ 2 ≤ c1) (h2 : v ^ 2 ≤ c2) : t ^ 2 ≤ 2 * (c1 + c2) := by
  have huv : 0 ≤ u + v := by linarith
  nlinarith [mul_le_mul htri htri ht huv, sq_nonneg (u - v), h1, h2, hu, hv]

end CurvatureCoefficientDifferenceJetTower

omit [NeZero (Module.finrank ℝ E)] in
theorem raisedKoszul_perOrder_l2_le_iteratedCovGrad_succ
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ^ 2 ≤
      10 * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T‖ ^ 2 := by
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
        10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x) := by
    intro x
    exact riemannianFiberNormSq_iteratedCovGrad_raisedKoszul_pointwise (I := I) (M := M) g₀ g₁ T htie n x
  have hF_int : MeasureTheory.Integrable
      (fun x => 10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (n + 1))
      (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T)).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (2 + n)
    (iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁))
    (fun x => 10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x))
    hF_int hpt
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 0
    (2 + (n + 1)) (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T)]
  rw [← SmoothCcTensor.norm_def]

theorem slotInsertEndoCc_ricEndoBackgroundDifferenceField_perOrder_l2_tameEnvelope
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  obtain ⟨C, hC_nn, hgrid⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 3),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
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
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hF_int : MeasureTheory.Integrable
        (fun x => C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (MeasureTheory.integrable_finsetSum _
        (fun k hk => (hKg P hPball k).1)).const_mul (C i)
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      hF_int
      (fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finsetSum _ (fun k hk => (hKg P hPball k).1)]
    have hsum_le : ∑ k ∈ Finset.range (i + 3),
          (∫ x, ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (∑ k ∈ Finset.range (i + 3), Kg k) *
          (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun k hk => ?_)
      refine le_trans (hKg P hPball k).2 ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKg_nn k)
      have hsub : ∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
          ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
        rw [Finset.mem_range] at hk
        omega
      linarith
    calc C i * ∑ k ∈ Finset.range (i + 3),
            (∫ x, ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ C i * ((∑ k ∈ Finset.range (i + 3), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum_le (hC_nn i)
      _ = (C i * ∑ k ∈ Finset.range (i + 3), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
          ring
  · have hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have hK_nn : 0 ≤ C i * ∑ k ∈ Finset.range (i + 3), Kg k :=
      mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k))
    nlinarith [hwin_nn, hK_nn]

theorem ricciOrderZeroRiemannCoeff_backgroundDifference_perOrder_l2_tameEnvelope
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  obtain ⟨C, hC_nn, hgrid⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciOrderZeroRiemannCoeff_backgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 3),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
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
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hF_int : MeasureTheory.Integrable
        (fun x => C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (MeasureTheory.integrable_finsetSum _
        (fun k hk => (hKg P hPball k).1)).const_mul (C i)
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀))
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      hF_int
      (fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finsetSum _ (fun k hk => (hKg P hPball k).1)]
    have hsum_le : ∑ k ∈ Finset.range (i + 3),
          (∫ x, ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (∑ k ∈ Finset.range (i + 3), Kg k) *
          (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun k hk => ?_)
      refine le_trans (hKg P hPball k).2 ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKg_nn k)
      have hsub : ∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
          ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
        rw [Finset.mem_range] at hk
        omega
      linarith
    calc C i * ∑ k ∈ Finset.range (i + 3),
            (∫ x, ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ C i * ((∑ k ∈ Finset.range (i + 3), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum_le (hC_nn i)
      _ = (C i * ∑ k ∈ Finset.range (i + 3), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
          ring
  · have hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have hK_nn : 0 ≤ C i * ∑ k ∈ Finset.range (i + 3), Kg k :=
      mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k))
    nlinarith [hwin_nn, hK_nn]

theorem ricciOrderZeroCurvCoeff_backgroundDifference_perOrder_l2_tameEnvelope
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  obtain ⟨K, hK_nn, hK⟩ :=
    slotInsertEndoCc_ricEndoBackgroundDifferenceField_perOrder_l2_tameEnvelope
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 4 * (Module.finrank ℝ E : ℝ) * K i,
    fun i => mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (hK_nn i), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hKi := hK g₁ P hδ_le hδ htie hPball i
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
        4 * (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) := by
    intro x
    have hsec : (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁ -
            ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x +
          (iteratedCovGrad (I := I) g₀ 2 2 i
            (reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
              (Equiv.swap (0 : Fin 2) 1))).toSection x := by
      rw [ricciOrderZeroCurvCoeff_backgroundDifference_decomp (I := I) (M := M) g₀ g₁,
        iteratedCovGrad_add (I := I) g₀ 2 2 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))
          (reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
            (Equiv.swap (0 : Fin 2) 1)),
        SmoothCcTensor.toSection_add]
      rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
    have hswap : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
            (Equiv.swap (0 : Fin 2) 1))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 2
        (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)) i x
    rw [hswap]
    have hendo : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) := by
      have h := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) i x
      rw [pow_one] at h
      exact h
    linarith [hendo]
  have hF_int : MeasureTheory.Integrable
      (fun x => 4 * (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁ -
        ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀))
    (fun x => 4 * (Module.finrank ℝ E : ℝ) *
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
    hF_int hpt
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 1 (1 + i)
    (iteratedCovGrad (I := I) g₀ 1 1 i
      (slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))]
  rw [← SmoothCcTensor.norm_def]
  calc 4 * (Module.finrank ℝ E : ℝ) *
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ ^ 2
      ≤ 4 * (Module.finrank ℝ E : ℝ) *
          (K i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left hKi ?_
        exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    _ = 4 * (Module.finrank ℝ E : ℝ) * K i *
          (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring

theorem ricciOrderZeroBaseCoeff_backgroundDifference_perOrder_l2_tameEnvelope
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              ((ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁) -
                (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ -
                  ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀))‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  obtain ⟨KR, hKR_nn, hKR⟩ :=
    ricciOrderZeroRiemannCoeff_backgroundDifference_perOrder_l2_tameEnvelope
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨KC, hKC_nn, hKC⟩ :=
    ricciOrderZeroCurvCoeff_backgroundDifference_perOrder_l2_tameEnvelope
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (KR i + KC i), fun i => by linarith [hKR_nn i, hKC_nn i], ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 3),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hR2 := hKR g₁ P hδ_le hδ htie hPball i
  have hC2 := hKC g₁ P hδ_le hδ htie hPball i
  have hre : (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁) -
      (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ -
        ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀) =
      (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀) -
      (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁ -
        ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀) := by
    abel
  rw [hre, iteratedCovGrad_sub (I := I) g₀ 2 2 i
    (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)
    (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁ -
      ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)]
  have hkey := tame_sq_le_two_add
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)
      - iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁ -
          ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁ -
          ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖
    (KR i * (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))
    (KC i * (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_sub_le _ _) hR2 hC2
  refine le_trans hkey (le_of_eq ?_)
  ring

theorem ricciOrderZeroBaseCoeff_perOrder_l2_tameEnvelope
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  obtain ⟨KD, hKD_nn, hKD⟩ :=
    ricciOrderZeroBaseCoeff_backgroundDifference_perOrder_l2_tameEnvelope
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (‖iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ -
        ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 + KD i),
    fun i => by
      linarith [hKD_nn i, sq_nonneg ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖], ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 3),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hD := hKD g₁ P hδ_le hδ htie hPball i
  have hsplit : ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁ =
      (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ -
        ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀) +
      ((ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁) -
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)) := by
    abel
  rw [hsplit, iteratedCovGrad_add (I := I) g₀ 2 2 i
    (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ -
      ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)
    ((ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁) -
      (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ -
        ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀))]
  have hbg_le : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ -
        ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 *
        (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    have hbg_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := sq_nonneg _
    nlinarith [hbg_nn, hwin_nn]
  have hkey := tame_sq_le_two_add
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)
      + iteratedCovGrad (I := I) g₀ 2 2 i
        ((ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁) -
          (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ -
            ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀))‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        ((ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁) -
          (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ -
            ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀))‖
    (‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 *
      (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))
    (KD i * (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_add_le _ _) hbg_le hD
  refine le_trans hkey (le_of_eq ?_)
  ring

end Spectral
end Analysis
end DifferentialGeometry

end
