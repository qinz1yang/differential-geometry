import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.Scalar
import DifferentialGeometry.Geometry.Operator.Family.Gram.Smoothness
import DifferentialGeometry.Analysis.Calculus.PartialDerivative.Parameter

noncomputable section

open Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem isSolutionOn_of_joint_metric
    (D : RealTimeInterval) (hD : UniqueDiffOn ℝ D.carrier)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (D.carrier ×ˢ (Set.univ : Set M)))
    (hflow : ∀ t ∈ D.regular, ∀ x (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g s).inner x v w)
        (-2 * ricciTensor (I := I) (g t) x v w) D.carrier t) :
    IsSolutionOn ({ base := { metric := g } } : SolutionOn (I := I) (M := M) D) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hgram := chartGramMatrix_joint_contMDiffOn g D.carrier hg
  apply isSolutionOn_of_reg g (metricFamilySmoothOn_of_contMDiffOn D g hg)
  · intro t ht x v w
    exact (hflow t ht x v w).hasDerivAt (D.regular_mem_nhds ht)
  · exact scalarCont_of_joint g D.carrier hD hgram
  · exact scalarTime_of_joint g D.carrier hD hgram
  · exact ricciCont_of_joint g D.carrier hD hgram
  · exact rm04Cont_of_joint g D.carrier hD hgram

end DifferentialGeometry.PDE.RicciFlow

end

noncomputable section

open Set Bundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.SolutionOn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

variable (S : SolutionOn (I := I) (M := M) D) (J : Set ℝ)
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun z : ℝ × M => (⟨z.2, (S.base.metric z.1).inner z.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set M)))

include hmetric

omit [I.Boundaryless] [T2Space M] in
private theorem chartGramFamilySmoothWithinOn_of_joint_metric (p : M) :
    chartGramFamilySmoothWithinOn (I := I) S.base.metric p J := by
  apply chartGramFamilySmoothWithinOn_of_contMDiffOn
  intro i j
  exact chartGramMatrix_joint_contMDiffOn S.base.metric J hmetric p i j

omit [T2Space M] in
theorem chartGram_spatial_fderiv_continuousOn_of_joint_metric (p : M) :
    ContinuousOn (fun z : ℝ × E => fderiv ℝ
      (fun y : E => chartGramOp (I := I) S.family p (z.1, y)) z.2)
      (J ×ˢ interior (extChartAt I p).target) := by
  apply chartGramOp_spatial_fderiv_continuousOn S.family p (fun _ hz => interior_subset hz.2)
  intro i j
  have hg : ContDiffOn ℝ ∞ (fun z : ℝ × E =>
      chartGramOnE (I := I) (S.base.metric z.1) p i j z.2)
      (J ×ˢ interior (extChartAt I p).target) :=
    fun _ hz => S.chartGramFamilySmoothWithinOn_of_joint_metric J hmetric p i j hz.1 hz.2
  exact (hg.iteratedFDeriv_snd (G := fun t y => chartGramOnE (I := I) (S.base.metric t) p i j y)
    isOpen_interior 1 (m := 0) (by simp)).continuousOn

theorem scalarOnE_spatial_fderiv_continuousOn_of_joint_metric (p : M) :
    ContinuousOn (fun z : ℝ × E => fderiv ℝ
      (DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := I) p (S.scalar z.1)) z.2)
      (J ×ˢ interior (extChartAt I p).target) := by
  have hg := scalarOnE_contDiffOn_of_chartGramFamilySmoothWithinOn S.base.metric p
    (S.chartGramFamilySmoothWithinOn_of_joint_metric J hmetric p)
  exact (hg.fderiv_snd
    (G := fun t y => DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := I) p (S.scalar t) y)
    isOpen_interior (m := 0) (by simp)).continuousOn

end DifferentialGeometry.PDE.RicciFlow.SolutionOn

end
