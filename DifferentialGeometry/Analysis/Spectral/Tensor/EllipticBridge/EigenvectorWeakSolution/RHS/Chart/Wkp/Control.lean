import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.Chart.Regularity
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.RotationSobolevBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.ChartWkpBounds.Uniform
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.RightDivergenceSobolevBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.Differentiated.Defs
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.LocalizedMultiplicationBound

open DifferentialGeometry.Analysis.Spectral
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


def eigenvectorResolventChartWkpRegularity
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ) : Prop :=
  ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
    MemWkp (d := Module.finrank ℝ E) (K + 1) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β)

section AggregateUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)

def resolventH1ComplChartWkpNorm (N : ℕ) (β : M)
    (Q : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i))
        β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
    (chartTargetEuclid (I := I) (M := M) β)

def eigenvectorChartComponentWkpNorm : ℝ≥0∞ :=
  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) α P₀ :
      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (chartTargetEuclid (I := I) (M := M) α)

def eigenvectorCrossLeftWkpControl : ℝ≥0∞ :=
  ∑ β ∈ transportChartCenters (I := I) (M := M) α,
    ((∑ Q : TensorCompIdx (E := E) r s,
        resolventH1ComplChartWkpNorm (I := I) (M := M) g r s i (K + 1) β Q)
      + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            resolventH1ComplChartWkpNorm (I := I) (M := M) g r s i (K + 1) β' Q)

def eigenvectorCrossRightWkpControl : ℝ≥0∞ :=
  ∑ β ∈ transportChartCenters (I := I) (M := M) α,
    ∑ Q : TensorCompIdx (E := E) r s,
      resolventH1ComplChartWkpNorm (I := I) (M := M) g r s i K β Q

def eigenvectorPartialLimitWkpNormSum : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    ∑ k : Fin (Module.finrank ℝ E),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((partialLpLimit (I := I) (M := M)
            g r s i α P k :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)

def eigenvectorComponentLimitWkpNormSum : ℝ≥0∞ :=
  ∑ p : TensorCompIdx (E := E) r s,
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => ((componentLpLimit (I := I) (M := M)
          g r s i α p :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α)

def eigenvectorCrossRightLimitWkpNormSum : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => ((crossRightLimitComponent (I := I) (M := M)
          g r s i α P :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α)

def eigenvectorCutoffPartialLimitWkpNormSum : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    ∑ l : Fin (Module.finrank ℝ E),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
            g r s i α P l :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)

def eigenvectorChartRHSWkpControl : ℝ≥0∞ :=
  eigenvectorChartComponentWkpNorm (I := I) (M := M) g r s i α P₀ K +
    eigenvectorCrossLeftWkpControl (I := I) (M := M) g r s i α K +
    eigenvectorCrossRightWkpControl (I := I) (M := M) g r s i α K +
    eigenvectorPartialLimitWkpNormSum (I := I) (M := M) g r s i α K +
    eigenvectorComponentLimitWkpNormSum (I := I) (M := M) g r s i α K +
    eigenvectorCrossRightLimitWkpNormSum (I := I) (M := M) g r s i α K +
    eigenvectorCutoffPartialLimitWkpNormSum (I := I) (M := M) g r s i α K

end AggregateUnconditional

private lemma le_sevenSum (a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ℝ≥0∞) :
    a₁ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₂ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₃ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₄ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₅ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₆ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₇ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc a₁ ≤ a₁ + a₂ := le_self_add
      _ ≤ a₁ + a₂ + a₃ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · calc a₂ ≤ a₁ + a₂ := le_add_self
      _ ≤ a₁ + a₂ + a₃ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · calc a₃ ≤ a₁ + a₂ + a₃ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · calc a₄ ≤ a₁ + a₂ + a₃ + a₄ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · calc a₅ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · calc a₆ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · exact le_add_self

section DominationUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)


omit [CompleteSpace E] in
lemma eigenvectorChartComponentWkpNorm_le_rhsWkpControl :
    eigenvectorChartComponentWkpNorm (I := I) (M := M) g r s i α P₀ K
      ≤ eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  rw [eigenvectorChartRHSWkpControl]; exact (le_sevenSum _ _ _ _ _ _ _).1


omit [CompleteSpace E] in
lemma eigenvectorCrossLeftWkpControl_le_rhsWkpControl :
    eigenvectorCrossLeftWkpControl (I := I) (M := M) g r s i α K
      ≤ eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  rw [eigenvectorChartRHSWkpControl]; exact (le_sevenSum _ _ _ _ _ _ _).2.1


omit [CompleteSpace E] in
lemma eigenvectorCrossRightWkpControl_le_rhsWkpControl :
    eigenvectorCrossRightWkpControl (I := I) (M := M) g r s i α K
      ≤ eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  rw [eigenvectorChartRHSWkpControl]; exact (le_sevenSum _ _ _ _ _ _ _).2.2.1


omit [CompleteSpace E] in
lemma eigenvectorPartialLimitWkpNormSum_le_rhsWkpControl :
    eigenvectorPartialLimitWkpNormSum (I := I) (M := M) g r s i α K
      ≤ eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  rw [eigenvectorChartRHSWkpControl]; exact (le_sevenSum _ _ _ _ _ _ _).2.2.2.1


omit [CompleteSpace E] in
lemma eigenvectorComponentLimitWkpNormSum_le_rhsWkpControl :
    eigenvectorComponentLimitWkpNormSum (I := I) (M := M) g r s i α K
      ≤ eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  rw [eigenvectorChartRHSWkpControl]
  exact (le_sevenSum _ _ _ _ _ _ _).2.2.2.2.1


omit [CompleteSpace E] in
lemma eigenvectorCrossRightLimitWkpNormSum_le_rhsWkpControl :
    eigenvectorCrossRightLimitWkpNormSum (I := I) (M := M) g r s i α K
      ≤ eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  rw [eigenvectorChartRHSWkpControl]
  exact (le_sevenSum _ _ _ _ _ _ _).2.2.2.2.2.1


omit [CompleteSpace E] in
lemma eigenvectorCutoffPartialLimitWkpNormSum_le_rhsWkpControl :
    eigenvectorCutoffPartialLimitWkpNormSum (I := I) (M := M) g r s i α K
      ≤ eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  rw [eigenvectorChartRHSWkpControl]
  exact (le_sevenSum _ _ _ _ _ _ _).2.2.2.2.2.2

omit [CompleteSpace E] in
lemma crossRightGradCoeffDivLimit_memWkp
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_term7_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartCrossRightDivergence (I := I) (M := M) g r s i α P₀) Ω :=
    eigenvectorChartCrossRightDivergence_memWkp (I := I) (M := M) g r s i α P₀ K h_pou
  have h_term7_ae_zero : ∀ᵐ y ∂(chartLebesgueMeasure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartCrossRightDivergence (I := I) (M := M) g r s i α P₀ y = 0 :=
    Filter.Eventually.of_forall (fun y hy_imp => by
      change (1 / densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y = 0
      rw [crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy_imp, mul_zero])
  obtain ⟨h_prod_memWkp, _⟩ := wkpNorm_smooth_coef_mul_ae_zero_factor_le
    (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (densityOnEuclid_contDiffOn (I := I) g α)
    h_term7_memWkp h_term7_ae_zero
  have h_ae_eq : (fun y => densityOnEuclid (I := I) g α y *
        eigenvectorChartCrossRightDivergence (I := I) (M := M) g r s i α P₀ y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ := by
    refine (ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    have hy' : y ∈ chartTargetEuclid (I := I) (M := M) α := hy
    have h_pos : densityOnEuclid (I := I) g α y ≠ 0 :=
      (densityOnEuclid_pos (I := I) g α hy').ne'
    change densityOnEuclid (I := I) g α y *
        ((1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y)
      = crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y
    rw [← mul_assoc, mul_one_div, div_self h_pos, one_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp

end DominationUnconditional

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
