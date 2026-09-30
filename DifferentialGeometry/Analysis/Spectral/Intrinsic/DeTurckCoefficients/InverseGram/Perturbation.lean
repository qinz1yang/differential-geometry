import DifferentialGeometry.Geometry.Metric.Coordinates.InverseGramPerturbation
import DifferentialGeometry.Geometry.Metric.Coordinates.JetDifference
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.Metric.InverseGramLowerBound
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Order.Compact
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator


noncomputable section


open Bundle Set Matrix
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Spectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

lemma exists_chartInvGramMatrix_entry_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source) :
    ∃ M_b : ℝ, 0 ≤ M_b ∧ ∀ x ∈ K, ∀ p q,
      |chartInvGramMatrix (I := I) g α x p q| ≤ M_b := by
  classical
  have h_cont : ContinuousOn
      (chartInvGramMatrixL1Sum (I := I) (M := M) g α) (chartAt H α).source :=
    chartInvGramMatrix_l1Sum_continuousOn (I := I) (M := M) g α
  have h_cont_K : ContinuousOn
      (chartInvGramMatrixL1Sum (I := I) (M := M) g α) K := h_cont.mono hKsub
  by_cases h_empty : K = ∅
  · exact ⟨0, le_refl 0, fun x hx => absurd (h_empty ▸ hx) (Set.notMem_empty _)⟩
  obtain ⟨C, hC⟩ := hK.bddAbove_image h_cont_K
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx p q
  have h_l1_le : chartInvGramMatrixL1Sum (I := I) (M := M) g α x ≤ C :=
    hC ⟨x, hx, rfl⟩
  have h_l1_eq :
      chartInvGramMatrixL1Sum (I := I) (M := M) g α x =
        Matrix.entrywiseL1 (chartInvGramMatrix (I := I) g α x) := rfl
  have h_entry_le :
      |chartInvGramMatrix (I := I) g α x p q| ≤
        chartInvGramMatrixL1Sum (I := I) (M := M) g α x := by
    rw [h_l1_eq]
    exact Matrix.abs_entry_le_entrywiseL1 (chartInvGramMatrix (I := I) g α x) p q
  exact h_entry_le.trans (h_l1_le.trans (le_max_left _ _))

theorem exists_chartInvGramMatrix_lipschitz_on_compact
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKsub : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ k l : Fin (Module.finrank ℝ E),
      |chartInvGramMatrix (I := I) g₁ α x k l -
          chartInvGramMatrix (I := I) g₂ α x k l| ≤
        C * DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) g₁ g₂ α x := by
  classical
  obtain ⟨M₁, hM₁_nn, hM₁⟩ :=
    exists_chartInvGramMatrix_entry_bound_on_compact (I := I) (M := M) g₁ α hK hKsub
  obtain ⟨M₂, hM₂_nn, hM₂⟩ :=
    exists_chartInvGramMatrix_entry_bound_on_compact (I := I) (M := M) g₂ α hK hKsub
  set M_b : ℝ := max M₁ M₂ with hM_def
  have hM_nn : 0 ≤ M_b := le_max_of_le_left hM₁_nn
  have h_base_eq :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source := rfl
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 + 1, ?_, ?_⟩
  · have h_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  intro x hx k l
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [h_base_eq]; exact hKsub hx
  have hM1' : ∀ p q, |chartInvGramMatrix (I := I) g₁ α x p q| ≤ M_b :=
    fun p q => (hM₁ x hx p q).trans (le_max_left _ _)
  have hM2' : ∀ p q, |chartInvGramMatrix (I := I) g₂ α x p q| ≤ M_b :=
    fun p q => (hM₂ x hx p q).trans (le_max_right _ _)
  have h_pt := chartInvGramMatrix_entry_sub_abs_le_chartGramDiffSum
    (I := I) (M := M) g₁ g₂ α hx_base hM1' hM2' k l
  have h_gram_nn : 0 ≤ DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) g₁ g₂ α x :=
    DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum_nonneg (I := I) (M := M) g₁ g₂ α x
  calc |chartInvGramMatrix (I := I) g₁ α x k l -
            chartInvGramMatrix (I := I) g₂ α x k l|
      ≤ (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 *
          DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) g₁ g₂ α x := h_pt
    _ ≤ ((Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 + 1) *
          DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) g₁ g₂ α x := by
        refine mul_le_mul_of_nonneg_right ?_ h_gram_nn
        linarith

theorem chartInvGram_pou_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∀ k₁ k₂ : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ p q : Fin (Module.finrank ℝ E),
            |chartInvGramMatrix (I := I) (gSeq k₁) α b p q -
                chartInvGramMatrix (I := I) (gSeq k₂) α b p q| ≤
              C * DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M)
                (gSeq k₁) (gSeq k₂) α b := by
  obtain ⟨M_b, hM_b, hM⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  let C : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro α hα k₁ k₂ b hb p q
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hpt := chartInvGramMatrix_entry_sub_abs_le_chartGramDiffSum
    (I := I) (M := M) (gSeq k₁) (gSeq k₂) α hb_base
      (hM α hα k₁ b hb) (hM α hα k₂ b hb) p q
  have hdiff_nonneg : 0 ≤ DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α b := DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum_nonneg _ _ _ _
  exact hpt.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hdiff_nonneg)

end DeTurckCoefficients
end Spectral
end Analysis
end DifferentialGeometry

end
