import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.Chart.Regularity
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRotationWkpNormBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderWkpNormBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRightDivWkpNormBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.Differentiated.Defs
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.LocalizedMultiplicationBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.Chart.Wkp.Control
open DifferentialGeometry.Geometry.Curvature

noncomputable section


open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Tensor.TensorRSRiemannian
open DifferentialGeometry.TensorRSNabla
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section Unconditional

section UniformTermBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)


omit [CompleteSpace E] in
private lemma resolventEigenvectorComponent_wkpNorm_le_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  refine ⟨1, by norm_num, fun i => ?_⟩
  rw [ENNReal.ofReal_one, one_mul]
  exact le_trans (le_of_eq rfl)
    (eigenvectorChartComponentWkpNorm_le_rhsWkpControl (I := I) (M := M) g r s i α P₀ K)


omit [CompleteSpace E] in
private lemma crossLeftBracketTerm_wkpNorm_le_uniform
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartCrossLeftContraction (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set F : (TensorCompIdx (E := E) r (s + 1) ×
        TensorCompIdx (E := E) r (s + 1)) →
      TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ :=
    fun x i y =>
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α x.1 x.2 y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
        ((crossLeftLimitComponent (I := I) (M := M)
          g r s i α x.1 :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have h_data : ∀ x : TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2 (F x i) Ω ∧
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F x i) Ω
              ≤ ENNReal.ofReal C *
                eigenvectorChartRHSWkpControl (I := I) (M := M)
                  g r s i α P₀ K := by
    intro x
    have hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => covChartMetricGram (I := I) (M := M) g r (s + 1) α x.1 x.2 y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ x.2 y) Ω :=
      (covChartMetricGram_contDiffOn (I := I) (M := M)
          g r (s + 1) α x.1 x.2).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ x.2)
    obtain ⟨C, hC_nn, hC_bd⟩ := wkpNorm_smooth_coef_mul_ae_zero_factor_le_uniform
      (I := I) (M := M) α K
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      hcoef_chart
    obtain ⟨C', hC'_nn, hC'_bd⟩ :=
      wkpNorm_crossLeftLimitComponent_le_uniform
        (I := I) (M := M) g r s K h_pou α x.1
    refine ⟨C * C', by positivity, fun i => ?_⟩
    have h_factor : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α x.1 :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      crossLeftLimitComponent_memWkp (I := I) (M := M)
        g r s i α x.1 K (h_pou i)
    have h_factor_ae_zero : ∀ᵐ y ∂(chartLebesgueMeasure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α x.1 :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
        (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α x.1
    obtain ⟨h_summand_memWkp, h_summand_bd⟩ := hC_bd
      (fun y => ((crossLeftLimitComponent (I := I) (M := M)
          g r s i α x.1 :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      h_factor h_factor_ae_zero
    refine ⟨h_summand_memWkp, ?_⟩
    have h_aggr_eq :
        (∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ((∑ Q : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s i))
                      β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β))
              + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                  ∑ Q : TensorCompIdx (E := E) r s,
                    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                            (eigenvectorResolvent (I := I) (M := M)
                              g r s i))
                          β' Q :
                          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) :
                          EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) β')))
          = eigenvectorCrossLeftWkpControl (I := I) (M := M) g r s i α K := by
      rw [eigenvectorCrossLeftWkpControl]; rfl
    calc
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F x i) Ω
          ≤ ENNReal.ofReal C *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((crossLeftLimitComponent (I := I) (M := M)
                    g r s i α x.1 :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω := h_summand_bd
      _ ≤ ENNReal.ofReal C *
            (ENNReal.ofReal C' *
              eigenvectorChartRHSWkpControl (I := I) (M := M)
                g r s i α P₀ K) := by
          gcongr
          rw [hΩ_def]
          refine (hC'_bd i).trans ?_
          rw [h_aggr_eq]
          gcongr
          exact eigenvectorCrossLeftWkpControl_le_rhsWkpControl (I := I) (M := M)
            g r s i α P₀ K
      _ = ENNReal.ofReal (C * C') *
            eigenvectorChartRHSWkpControl (I := I) (M := M)
              g r s i α P₀ K := by
          rw [ENNReal.ofReal_mul hC_nn, mul_assoc]
  choose Cx hCx_nn hCx using h_data
  obtain ⟨C, hC_nn, hC_bd⟩ := wkpNorm_sum_le_of_le_ofReal_mul_uniform
    (Ω := Ω) (by norm_num) hΩ_open F
    (fun i => eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K)
    (fun x i => (hCx x i).1)
    (fun x => ⟨Cx x, hCx_nn x, fun i => (hCx x i).2⟩)
  refine ⟨C, hC_nn, fun i => ?_⟩
  have h_eq : eigenvectorChartCrossLeftContraction (I := I) (M := M) g r s i α P₀
      = fun y => ∑ x : TensorCompIdx (E := E) r (s + 1) ×
          TensorCompIdx (E := E) r (s + 1), F x i y := by
    funext y
    simp only [eigenvectorChartCrossLeftContraction, hF_def, Fintype.sum_prod_type]
  rw [h_eq, hΩ_def]
  exact hC_bd i


omit [CompleteSpace E] in
private lemma crossRightBracketTerm_wkpNorm_le_uniform
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartCrossRightContraction (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set F : (TensorCompIdx (E := E) r s ×
        TensorCompIdx (E := E) r s) →
      TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ :=
    fun x i y =>
      (covChartMetricGram (I := I) (M := M) g r s α x.1 x.2 y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
        ((crossRightLimitComponent (I := I) (M := M)
          g r s i α x.1 :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have h_pou_K : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) :=
    fun i β Q => (h_pou i β Q).le_of_le (Nat.le_succ K)
  have h_data : ∀ x : TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2 (F x i) Ω ∧
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F x i) Ω
              ≤ ENNReal.ofReal C *
                eigenvectorChartRHSWkpControl (I := I) (M := M)
                  g r s i α P₀ K := by
    intro x
    have hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => covChartMetricGram (I := I) (M := M) g r s α x.1 x.2 y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ x.2 y) Ω :=
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α x.1 x.2).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ x.2)
    obtain ⟨C, hC_nn, hC_bd⟩ := wkpNorm_smooth_coef_mul_ae_zero_factor_le_uniform
      (I := I) (M := M) α K
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      hcoef_chart
    obtain ⟨C', hC'_nn, hC'_bd⟩ :=
      wkpNorm_crossRightLimitComponent_le_uniform
        (I := I) (M := M) g r s K h_pou_K α x.1
    refine ⟨C * C', by positivity, fun i => ?_⟩
    have h_factor : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((crossRightLimitComponent (I := I) (M := M)
            g r s i α x.1 :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      crossRightLimitComponent_memWkp (I := I) (M := M)
        g r s i α x.1 K (h_pou i)
    have h_factor_ae_zero : ∀ᵐ y ∂(chartLebesgueMeasure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossRightLimitComponent (I := I) (M := M)
              g r s i α x.1 :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
        (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α x.1
    obtain ⟨h_summand_memWkp, h_summand_bd⟩ := hC_bd
      (fun y => ((crossRightLimitComponent (I := I) (M := M)
          g r s i α x.1 :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      h_factor h_factor_ae_zero
    refine ⟨h_summand_memWkp, ?_⟩
    have h_aggr_eq :
        (∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
                    β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β))
          = eigenvectorCrossRightWkpControl (I := I) (M := M) g r s i α K := by
      rw [eigenvectorCrossRightWkpControl]; rfl
    calc
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F x i) Ω
          ≤ ENNReal.ofReal C *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((crossRightLimitComponent (I := I)
                    (M := M) g r s i α x.1 :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω := h_summand_bd
      _ ≤ ENNReal.ofReal C *
            (ENNReal.ofReal C' *
              eigenvectorChartRHSWkpControl (I := I) (M := M)
                g r s i α P₀ K) := by
          gcongr
          rw [hΩ_def]
          refine (hC'_bd i).trans ?_
          rw [h_aggr_eq]
          gcongr
          exact eigenvectorCrossRightWkpControl_le_rhsWkpControl (I := I) (M := M)
            g r s i α P₀ K
      _ = ENNReal.ofReal (C * C') *
            eigenvectorChartRHSWkpControl (I := I) (M := M)
              g r s i α P₀ K := by
          rw [ENNReal.ofReal_mul hC_nn, mul_assoc]
  choose Cx hCx_nn hCx using h_data
  obtain ⟨C, hC_nn, hC_bd⟩ := wkpNorm_sum_le_of_le_ofReal_mul_uniform
    (Ω := Ω) (by norm_num) hΩ_open F
    (fun i => eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K)
    (fun x i => (hCx x i).1)
    (fun x => ⟨Cx x, hCx_nn x, fun i => (hCx x i).2⟩)
  refine ⟨C, hC_nn, fun i => ?_⟩
  have h_eq : eigenvectorChartCrossRightContraction (I := I) (M := M) g r s i α P₀
      = fun y => ∑ x : TensorCompIdx (E := E) r s ×
          TensorCompIdx (E := E) r s, F x i y := by
    funext y
    simp only [eigenvectorChartCrossRightContraction, hF_def, Fintype.sum_prod_type]
  rw [h_eq, hΩ_def]
  exact hC_bd i


omit [CompleteSpace E] in
private lemma principalRotationCoeffTerm_wkpNorm_le_uniform
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    wkpNorm_covPrincipalRotationCoeffLimit_le_uniform
      (I := I) (M := M) g r s K α P₀ h_pou
  refine ⟨C, hC_nn, fun i => ?_⟩
  refine le_trans (hC_bd i) ?_
  gcongr
  exact eigenvectorPartialLimitWkpNormSum_le_rhsWkpControl (I := I) (M := M) g r s i α P₀ K


omit [CompleteSpace E] in
private lemma lowerOrderRotationCoeffTerm_wkpNorm_le_uniform
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (covLowerOrderRotationValueCoeffLimit (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    wkpNorm_covLowerOrderRotationValueCoeffLimit_le_uniform
      (I := I) (M := M) g r s K α P₀ h_pou
  refine ⟨2 * C, by positivity, fun i => ?_⟩
  have h_sum_le :
      eigenvectorPartialLimitWkpNormSum (I := I) (M := M) g r s i α K
          + eigenvectorComponentLimitWkpNormSum (I := I) (M := M) g r s i α K
        ≤ 2 * eigenvectorChartRHSWkpControl (I := I) (M := M)
            g r s i α P₀ K := by
    rw [two_mul]
    exact add_le_add
      (eigenvectorPartialLimitWkpNormSum_le_rhsWkpControl (I := I) (M := M) g r s i α P₀ K)
      (eigenvectorComponentLimitWkpNormSum_le_rhsWkpControl (I := I) (M := M) g r s i α P₀ K)
  refine le_trans (hC_bd i) ?_
  calc
    ENNReal.ofReal C *
        (eigenvectorPartialLimitWkpNormSum (I := I) (M := M) g r s i α K
          + eigenvectorComponentLimitWkpNormSum (I := I) (M := M) g r s i α K)
        ≤ ENNReal.ofReal C *
            (2 * eigenvectorChartRHSWkpControl (I := I) (M := M)
              g r s i α P₀ K) := by
          gcongr
    _ = ENNReal.ofReal (2 * C) *
          eigenvectorChartRHSWkpControl (I := I) (M := M)
            g r s i α P₀ K := by
        rw [← ENNReal.ofReal_ofNat 2, ← mul_assoc, ← ENNReal.ofReal_mul hC_nn, mul_comm C 2]


omit [CompleteSpace E] in
private lemma weightedGradCoeffDivLimit_sum_wkpNorm_le_uniform
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_data : ∀ l : Fin (Module.finrank ℝ E),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2
              (weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l) Ω ∧
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (weightedGradCoeffDivLimit (I := I) (M := M)
                  g r s i α P₀ l) Ω
              ≤ ENNReal.ofReal C *
                eigenvectorChartRHSWkpControl (I := I) (M := M)
                  g r s i α P₀ K := by
    intro l
    obtain ⟨C, hC_nn, hC_bd⟩ :=
      wkpNorm_weightedGradCoeffDivLimit_le_uniform
        (I := I) (M := M) g r s K α P₀ l h_pou
    refine ⟨2 * C, by positivity, fun i => ?_⟩
    refine ⟨?_, ?_⟩
    · rw [hΩ_def]
      exact weightedGradCoeffDivLimit_memWkp (I := I) (M := M)
        g r s i α P₀ l K (fun β Q => h_pou i β Q)
    rw [hΩ_def]
    refine le_trans (hC_bd i) ?_
    have h_sum_le :
        eigenvectorComponentLimitWkpNormSum (I := I) (M := M) g r s i α K
            + eigenvectorPartialLimitWkpNormSum (I := I) (M := M) g r s i α K
          ≤ 2 * eigenvectorChartRHSWkpControl (I := I) (M := M)
              g r s i α P₀ K := by
      rw [two_mul]
      exact add_le_add
        (eigenvectorComponentLimitWkpNormSum_le_rhsWkpControl (I := I) (M := M) g r s i α P₀ K)
        (eigenvectorPartialLimitWkpNormSum_le_rhsWkpControl (I := I) (M := M) g r s i α P₀ K)
    calc
      ENNReal.ofReal C *
          (eigenvectorComponentLimitWkpNormSum (I := I) (M := M) g r s i α K
            + eigenvectorPartialLimitWkpNormSum (I := I) (M := M) g r s i α K)
          ≤ ENNReal.ofReal C *
              (2 * eigenvectorChartRHSWkpControl (I := I) (M := M)
                g r s i α P₀ K) := by
            gcongr
      _ = ENNReal.ofReal (2 * C) *
            eigenvectorChartRHSWkpControl (I := I) (M := M)
              g r s i α P₀ K := by
          rw [← ENNReal.ofReal_ofNat 2, ← mul_assoc, ← ENNReal.ofReal_mul hC_nn,
            mul_comm C 2]
  choose Cl hCl_nn hCl using h_data
  obtain ⟨C, hC_nn, hC_bd⟩ := wkpNorm_sum_le_of_le_ofReal_mul_uniform
    (Ω := Ω) (by norm_num) hΩ_open
    (fun l i => weightedGradCoeffDivLimit (I := I) (M := M)
      g r s i α P₀ l)
    (fun i => eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K)
    (fun l i => (hCl l i).1)
    (fun l => ⟨Cl l, hCl_nn l, fun i => (hCl l i).2⟩)
  exact ⟨C, hC_nn, fun i => hC_bd i⟩


omit [CompleteSpace E] in
private lemma weightedGradDivTerm_wkpNorm_le_uniform
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartWeightedDivergence (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ := wkpNorm_smooth_coef_mul_ae_zero_factor_le_uniform
    (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ :=
    weightedGradCoeffDivLimit_sum_wkpNorm_le_uniform
      (I := I) (M := M) g r s α P₀ K h_pou
  refine ⟨C₁ * C₂, by positivity, fun i => ?_⟩
  have h_sum_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        weightedGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ l y) Ω :=
    MemWkp.finset_sum (by norm_num) hΩ_open
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l => weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l)
      (fun l _ => weightedGradCoeffDivLimit_memWkp (I := I) (M := M)
        g r s i α P₀ l K (fun β Q => h_pou i β Q))
  have h_sum_ae_zero : ∀ᵐ y ∂(chartLebesgueMeasure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y) = 0 :=
    Filter.Eventually.of_forall (fun _y hy =>
      Finset.sum_eq_zero (fun l _ =>
        weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ l hy))
  obtain ⟨_, h_coef_bd⟩ := hC₁_bd
    (fun y => ∑ l : Fin (Module.finrank ℝ E),
      weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l y)
    h_sum_memWkp h_sum_ae_zero
  have h_term6_eq : eigenvectorChartWeightedDivergence (I := I) (M := M) g r s i α P₀
      = fun y => (1 / densityOnEuclid (I := I) g α y) *
          (∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l y) := rfl
  rw [h_term6_eq]
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => (1 / densityOnEuclid (I := I) g α y) *
          (∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l y)) Ω
        ≤ ENNReal.ofReal C₁ *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ l : Fin (Module.finrank ℝ E),
                weightedGradCoeffDivLimit (I := I) (M := M)
                  g r s i α P₀ l y) Ω := h_coef_bd
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            eigenvectorChartRHSWkpControl (I := I) (M := M)
              g r s i α P₀ K) := by
        gcongr
        exact hC₂_bd i
    _ = ENNReal.ofReal (C₁ * C₂) *
          eigenvectorChartRHSWkpControl (I := I) (M := M)
            g r s i α P₀ K := by
        rw [ENNReal.ofReal_mul hC₁_nn, mul_assoc]


omit [CompleteSpace E] in
private lemma crossRightGradDivTerm_wkpNorm_le_uniform
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartCrossRightDivergence (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ := wkpNorm_smooth_coef_mul_ae_zero_factor_le_uniform
    (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ :=
    wkpNorm_crossRightGradCoeffDivLimit_le_uniform
      (I := I) (M := M) g r s α P₀ K h_pou
  refine ⟨C₁ * (2 * C₂), by positivity, fun i => ?_⟩
  have h_div_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀) Ω :=
    crossRightGradCoeffDivLimit_memWkp (I := I) (M := M)
      g r s i α P₀ K (fun β Q => h_pou i β Q)
  have h_div_ae_zero : ∀ᵐ y ∂(chartLebesgueMeasure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y = 0 :=
    Filter.Eventually.of_forall (fun y hy_imp =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy_imp)
  obtain ⟨_, h_coef_bd⟩ := hC₁_bd
    (crossRightGradCoeffDivLimit (I := I) (M := M)
      g r s i α P₀)
    h_div_memWkp h_div_ae_zero
  have h_term7_eq : eigenvectorChartCrossRightDivergence (I := I) (M := M) g r s i α P₀
      = fun y => (1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y := rfl
  rw [h_term7_eq]
  have h_sum_le :
      eigenvectorCrossRightLimitWkpNormSum (I := I) (M := M) g r s i α K
          + eigenvectorCutoffPartialLimitWkpNormSum (I := I) (M := M) g r s i α K
        ≤ 2 * eigenvectorChartRHSWkpControl (I := I) (M := M)
            g r s i α P₀ K := by
    rw [two_mul]
    exact add_le_add
      (eigenvectorCrossRightLimitWkpNormSum_le_rhsWkpControl (I := I) (M := M) g r s i α P₀ K)
      (eigenvectorCutoffPartialLimitWkpNormSum_le_rhsWkpControl (I := I) (M := M) g r s i α P₀ K)
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => (1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y) Ω
        ≤ ENNReal.ofReal C₁ *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (crossRightGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀) Ω := h_coef_bd
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            (2 * eigenvectorChartRHSWkpControl (I := I) (M := M)
              g r s i α P₀ K)) := by
        gcongr
        refine le_trans (hC₂_bd i) ?_
        gcongr
        exact h_sum_le
    _ = ENNReal.ofReal (C₁ * (2 * C₂)) *
          eigenvectorChartRHSWkpControl (I := I) (M := M)
            g r s i α P₀ K := by
        rw [ENNReal.ofReal_mul hC₁_nn,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat 2]
        ring

end UniformTermBoundsUnconditional

section UniformBracketBoundUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)


omit [CompleteSpace E] in
lemma eigenvectorChartRHSNumerator_wkpNorm_le_uniform
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartRHSNumerator (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  classical
  obtain ⟨D1, hD1_nn, hD1⟩ := resolventEigenvectorComponent_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ K
  obtain ⟨D2, hD2_nn, hD2⟩ := crossLeftBracketTerm_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ K h_pou
  obtain ⟨D3, hD3_nn, hD3⟩ := crossRightBracketTerm_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ K h_pou
  obtain ⟨D4, hD4_nn, hD4⟩ := principalRotationCoeffTerm_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ K h_pou
  obtain ⟨D5, hD5_nn, hD5⟩ := lowerOrderRotationCoeffTerm_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ K h_pou
  obtain ⟨D6, hD6_nn, hD6⟩ := weightedGradDivTerm_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ K h_pou
  obtain ⟨D7, hD7_nn, hD7⟩ := crossRightGradDivTerm_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ K h_pou
  refine ⟨D1 + D2 + D3 + D4 + D5 + D6 + D7, by positivity, fun i => ?_⟩
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hM1 := eigenvectorChartComponentFun_memWkp (I := I) (M := M)
    g r s i α P₀ K (h_pou i)
  have hM2 := eigenvectorChartCrossLeftContraction_memWkp (I := I) (M := M)
    g r s i α P₀ K (h_pou i)
  have hM3 := eigenvectorChartCrossRightContraction_memWkp (I := I) (M := M)
    g r s i α P₀ K (h_pou i)
  have hM4 := covPrincipalRotationCoeffLimit_memWkp (I := I) (M := M)
    g r s i α P₀ K (h_pou i)
  have hM5 := covLowerOrderRotationValueCoeffLimit_memWkp (I := I) (M := M)
    g r s i α P₀ K (h_pou i)
  have hM6 := eigenvectorChartWeightedDivergence_memWkp (I := I) (M := M)
    g r s i α P₀ K (h_pou i)
  have hM7 := eigenvectorChartCrossRightDivergence_memWkp (I := I) (M := M)
    g r s i α P₀ K (h_pou i)
  rw [← hΩ_def] at hM1 hM2 hM3 hM4 hM5 hM6 hM7
  have hp2 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hB12 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀ y
        - eigenvectorChartCrossLeftContraction (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open hM1 hM2
  have hB123 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀ y
          - eigenvectorChartCrossLeftContraction (I := I) (M := M) g r s i α P₀ y)
        + eigenvectorChartCrossRightContraction (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.add (d := Module.finrank ℝ E) hp2 hΩ_open hB12 hM3
  have hB1234 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀ y
            - eigenvectorChartCrossLeftContraction (I := I) (M := M) g r s i α P₀ y)
          + eigenvectorChartCrossRightContraction (I := I) (M := M) g r s i α P₀ y)
        - covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open hB123 hM4
  have hB12345 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (((eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀ y
              - eigenvectorChartCrossLeftContraction (I := I) (M := M) g r s i α P₀ y)
            + eigenvectorChartCrossRightContraction (I := I) (M := M) g r s i α P₀ y)
          - covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀ y)
        - covLowerOrderRotationValueCoeffLimit (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open hB1234 hM5
  have hB123456 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((((eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀ y
                - eigenvectorChartCrossLeftContraction (I := I) (M := M) g r s i α P₀ y)
              + eigenvectorChartCrossRightContraction (I := I) (M := M) g r s i α P₀ y)
            - covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀ y)
          - covLowerOrderRotationValueCoeffLimit (I := I) (M := M) g r s i α P₀ y)
        + eigenvectorChartWeightedDivergence (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.add (d := Module.finrank ℝ E) hp2 hΩ_open hB12345 hM6
  have hD1i := hD1 i
  have hD2i := hD2 i
  have hD3i := hD3 i
  have hD4i := hD4 i
  have hD5i := hD5 i
  have hD6i := hD6 i
  have hD7i := hD7 i
  have h_tri :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHSNumerator (I := I) (M := M) g r s i α P₀) Ω
        ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartCrossLeftContraction (I := I) (M := M) g r s i α P₀) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartCrossRightContraction (I := I) (M := M) g r s i α P₀) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (covLowerOrderRotationValueCoeffLimit (I := I) (M := M) g r s i α P₀) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartWeightedDivergence (I := I) (M := M) g r s i α P₀) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartCrossRightDivergence (I := I) (M := M) g r s i α P₀) Ω := by
    have h_bracket_eq :
        eigenvectorChartRHSNumerator (I := I) (M := M) g r s i α P₀
        = fun y =>
            (((((eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀ y
                  - eigenvectorChartCrossLeftContraction (I := I) (M := M) g r s i α P₀ y)
                + eigenvectorChartCrossRightContraction (I := I) (M := M) g r s i α P₀ y)
              - covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀ y)
            - covLowerOrderRotationValueCoeffLimit (I := I) (M := M) g r s i α P₀ y)
          + eigenvectorChartWeightedDivergence (I := I) (M := M) g r s i α P₀ y)
          - eigenvectorChartCrossRightDivergence (I := I) (M := M) g r s i α P₀ y := by
      funext y
      simp only [eigenvectorChartRHSNumerator, Pi.sub_apply, Pi.add_apply]
    rw [h_bracket_eq]
    refine le_trans (wkpNorm_sub_le (k := K) (by norm_num) hΩ_open hB123456 hM7) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (wkpNorm_add_le (d := Module.finrank ℝ E)
      (by norm_num) hΩ_open hB12345 hM6) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (wkpNorm_sub_le (k := K) (by norm_num) hΩ_open hB1234 hM5) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (wkpNorm_sub_le (k := K) (by norm_num) hΩ_open hB123 hM4) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (wkpNorm_add_le (d := Module.finrank ℝ E)
      (by norm_num) hΩ_open hB12 hM3) ?_
    refine add_le_add ?_ (le_refl _)
    exact wkpNorm_sub_le (k := K) (by norm_num) hΩ_open hM1 hM2
  refine le_trans h_tri ?_
  have h_seven :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀) Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartCrossLeftContraction (I := I) (M := M) g r s i α P₀) Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartCrossRightContraction (I := I) (M := M) g r s i α P₀) Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀) Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (covLowerOrderRotationValueCoeffLimit (I := I) (M := M) g r s i α P₀) Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartWeightedDivergence (I := I) (M := M) g r s i α P₀) Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartCrossRightDivergence (I := I) (M := M) g r s i α P₀) Ω
      ≤ ENNReal.ofReal D1 *
            eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D2 *
            eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D3 *
            eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D4 *
            eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D5 *
            eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D6 *
            eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D7 *
            eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K :=
    add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add hD1i hD2i) hD3i) hD4i) hD5i) hD6i) hD7i
  refine le_trans h_seven ?_
  rw [ENNReal.ofReal_add (by positivity) hD7_nn,
    ENNReal.ofReal_add (by positivity) hD6_nn,
    ENNReal.ofReal_add (by positivity) hD5_nn,
    ENNReal.ofReal_add (by positivity) hD4_nn,
    ENNReal.ofReal_add (by positivity) hD3_nn,
    ENNReal.ofReal_add hD1_nn hD2_nn]
  rw [add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]

end UniformBracketBoundUnconditional

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
