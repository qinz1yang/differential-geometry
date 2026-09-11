import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity

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
