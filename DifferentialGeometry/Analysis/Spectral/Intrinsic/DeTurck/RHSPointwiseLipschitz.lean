import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricDifferenceJetNorm
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature

noncomputable section


open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor
open DifferentialGeometry.Analysis.Sobolev.HebeyBlock
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Parabolic DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M]

attribute [local instance]
  rhsPointwiseModelDualNormedAddCommGroup
  rhsPointwiseModelDualNormedSpace
  rhsPointwiseModelBilinearNormedAddCommGroup
  rhsPointwiseModelBilinearNormedSpace
  rhsPointwiseModelTrilinearNormedAddCommGroup
  rhsPointwiseModelTrilinearNormedSpace
  rhsPointwiseModelQuadrilinearNormedAddCommGroup
  rhsPointwiseModelQuadrilinearNormedSpace
  rhsPointwiseTangentDualNormedAddCommGroup
  rhsPointwiseTangentDualNormedSpace
  rhsPointwiseTangentBilinearNormedAddCommGroup
  rhsPointwiseTangentBilinearNormedSpace
  rhsPointwiseTangentTrilinearNormedAddCommGroup
  rhsPointwiseTangentTrilinearNormedSpace
  rhsPointwiseTangentTrilinearAddCommGroup
  rhsPointwiseTangentTrilinearModule
  rhsPointwiseTangentTrilinearSMul
  rhsPointwiseTangentTrilinearTopology
  rhsPointwiseSectionAddCommGroup
  rhsPointwiseSectionModule
  rhsPointwiseTangentQuadrilinearNormedAddCommGroup
  rhsPointwiseTangentQuadrilinearNormedSpace
  rhsPointwiseTangentQuadrilinearAddCommGroup
  rhsPointwiseTangentQuadrilinearModule
  rhsPointwiseTangentBilinearAddCommGroup
  rhsPointwiseTangentBilinearModule
  rhsPointwiseBilinearSectionAddCommGroup
  rhsPointwiseBilinearSectionModule
  rhsPointwiseTensor0SModelNormedAddCommGroup
  rhsPointwiseTensor0SModelNormedSpace
  rhsPointwiseTensorRSModelNormedAddCommGroup
  rhsPointwiseTensorRSModelNormedSpace
  rhsPointwiseTensor01TotalSpaceTopology
  rhsPointwiseTensor01FiberBundle
  rhsPointwiseTensor01VectorBundle
  rhsPointwiseTensor01ContMDiffVectorBundle
  rhsPointwiseTensor02TotalSpaceTopology
  rhsPointwiseIteratedTensor02FiberBundle
  rhsPointwiseIteratedTensor02VectorBundle
  rhsPointwiseIteratedTensor02ContMDiffVectorBundle
  rhsPointwiseTensor03TotalSpaceTopology
  rhsPointwiseTensor03FiberBundle
  rhsPointwiseTensor03VectorBundle
  rhsPointwiseTensor03ContMDiffVectorBundle
  rhsPointwiseTensor04TotalSpaceTopology
  rhsPointwiseTensor04FiberBundle
  rhsPointwiseTensor04VectorBundle
  rhsPointwiseTensor04ContMDiffVectorBundle
  rhsPointwiseTensorRSTotalSpaceTopology
  rhsPointwiseTensorRSFiberBundle

private local instance rhsPointwiseTensorRSNormedAddCommGroup
    (r s : ℕ) [Bundle.RiemannianBundle (fun y : M => TensorRSSpace r s I y)] (x : M) :
    NormedAddCommGroup (TensorRSSpace r s I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TensorRSSpace r s I y) x

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckRHS_diff_frame_component_apply
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (deTurckRicciRHS (I := I) g_bg g₁ x - deTurckRicciRHS (I := I) g_bg g₂ x)
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      deTurckRicciRHS (I := I) g_bg g₁ x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)
      - deTurckRicciRHS (I := I) g_bg g₂ x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) := by
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]






omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckRHS_diff_frame_component_contMDiffOn
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        (deTurckRicciRHS (I := I) g_bg g₁ x - deTurckRicciRHS (I := I) g_bg g₂ x)
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source := by
  have h₁ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => deTurckRicciRHS (I := I) g_bg g₁ x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source :=
    combine_smoothness_of_summands (I := I) g_bg g₁ α i j
  have h₂ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => deTurckRicciRHS (I := I) g_bg g₂ x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source :=
    combine_smoothness_of_summands (I := I) g_bg g₂ α i j
  refine (h₁.sub h₂).congr (fun x _ => ?_)
  exact deTurckRHS_diff_frame_component_apply (I := I) g_bg g₁ g₂ α x i j

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    in
theorem deTurckRHS_diff_gNorm_le_modelNorm_pointwise
    (g₀ : SmoothRiemannianMetric I M) (x₀ : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
    ∃ D : ℝ, 0 < D ∧ ∀ T : TensorRSSpace 0 2 I x₀,
      ‖T‖ ≤ D * ‖TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T‖ :=
  gNorm_le_modelNorm_pointwise (I := I) (M := M) g₀ 0 2 x₀










def chartDeTurckRHSComp (g_bg g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (-2 : ℝ) * chartRicciTensor (I := I) g α i j y
    + chartLieDeTurckComp (I := I) g g_bg α i j y

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    in
@[simp] theorem chartDeTurckRHSComp_def (g_bg g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckRHSComp (I := I) g_bg g α i j y =
      (-2 : ℝ) * chartRicciTensor (I := I) g α i j y
        + chartLieDeTurckComp (I := I) g g_bg α i j y := rfl



























omit [CompactSpace M] in
omit [I.Boundaryless] [T2Space M] in
theorem exists_chartDeTurckRHSComp_lipschitz_on_compact
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
      |chartDeTurckRHSComp (I := I) g_bg g₁ α i j y -
          chartDeTurckRHSComp (I := I) g_bg g₂ α i j y| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  obtain ⟨Cric, hCric_pos, hCric⟩ :=
    DeTurckCoefficients.exists_chartRicciTensor_lipschitz_on_compact
      (I := I) (M := M) g₁ g₂ α hK hKsub
  obtain ⟨Clie, hClie_pos, hClie⟩ :=
    DeTurckCoefficients.exists_chartLieDeTurckComp_lipschitz_on_compact
      (I := I) (M := M) g₁ g₂ g_bg α hK hKsub
  refine ⟨2 * Cric + Clie, ?_, ?_⟩
  · have h1 : 0 < 2 * Cric := by positivity
    linarith
  intro y hy i j
  have hjet2_nn : 0 ≤ chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y :=
    DeTurckCoefficients.chartMetricJet2DiffSup_nonneg _ _ _ _
  set jet2 : ℝ := chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y with hjet2_def
  have hsplit :
      chartDeTurckRHSComp (I := I) g_bg g₁ α i j y -
          chartDeTurckRHSComp (I := I) g_bg g₂ α i j y =
        (-2 : ℝ) * (chartRicciTensor (I := I) g₁ α i j y -
              chartRicciTensor (I := I) g₂ α i j y)
          + (chartLieDeTurckComp (I := I) g₁ g_bg α i j y -
              chartLieDeTurckComp (I := I) g₂ g_bg α i j y) := by
    rw [chartDeTurckRHSComp_def, chartDeTurckRHSComp_def]; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have hric_bound : |(-2 : ℝ) * (chartRicciTensor (I := I) g₁ α i j y -
        chartRicciTensor (I := I) g₂ α i j y)| ≤ 2 * Cric * jet2 := by
    rw [abs_mul]
    have h2 : |(-2 : ℝ)| = 2 := by norm_num
    rw [h2]
    have hR := hCric y hy i j
    calc 2 * |chartRicciTensor (I := I) g₁ α i j y -
            chartRicciTensor (I := I) g₂ α i j y|
        ≤ 2 * (Cric * jet2) :=
          mul_le_mul_of_nonneg_left hR (by norm_num)
      _ = 2 * Cric * jet2 := by ring
  have hlie_bound : |chartLieDeTurckComp (I := I) g₁ g_bg α i j y -
        chartLieDeTurckComp (I := I) g₂ g_bg α i j y| ≤ Clie * jet2 :=
    hClie y hy i j
  calc |(-2 : ℝ) * (chartRicciTensor (I := I) g₁ α i j y -
            chartRicciTensor (I := I) g₂ α i j y)|
        + |chartLieDeTurckComp (I := I) g₁ g_bg α i j y -
            chartLieDeTurckComp (I := I) g₂ g_bg α i j y|
      ≤ 2 * Cric * jet2 + Clie * jet2 := add_le_add hric_bound hlie_bound
    _ = (2 * Cric + Clie) * jet2 := by ring


end Spectral
end Analysis
end DifferentialGeometry

end
