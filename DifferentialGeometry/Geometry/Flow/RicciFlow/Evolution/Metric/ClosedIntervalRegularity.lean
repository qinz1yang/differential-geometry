import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabChartBootstrap
import DifferentialGeometry.Geometry.Metric.Family.Continuity

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set Bundle Manifold Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)]

theorem solution_metric_tensor_contMDiffOn_closed
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (S.base.metric p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc c b ×ˢ (univ : Set M)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply metricCLMSection_jointContMDiffOn_of_chartGram_on
  intro x₀ i j
  have hcoord := Perelman.CanonicalNeighborhood.FiniteHorn.chartGram_contDiffOn_of_spatialJets
    (fun t => S.base.metric t) x₀ hcb (isOpen_extChartAt_target x₀) Subset.rfl
    (Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_jets_continuousOn_closed
      S hS hac hcb hslab hregular x₀) (fun t ht x v w => by
        simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
          metricRicciAt_apply_eq_ricciTensor, SolutionOn.family_metric] using
          metricDerivAt S hS ⟨t, hregular ⟨hac.trans ht.1, ht.2⟩⟩ x v w)
  have he := (contDiffOn_pi.mp (contDiffOn_pi.mp hcoord i)) j
  have hself : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × E => chartGramOnE (S.base.metric p.1) x₀ i j p.2)
      (Icc c b ×ˢ interior (extChartAt I x₀).target) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (he.mono (prod_mono Subset.rfl interior_subset)).contMDiffOn
  have hc : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => (p.1, extChartAt I x₀ p.2))
      (Icc c b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    apply contMDiffOn_fst.prodMk
    apply (contMDiffOn_extChartAt (I := I) (x := x₀)).comp contMDiffOn_snd
    intro p hp
    exact hp.2
  have hm : MapsTo (fun p : ℝ × M => (p.1, extChartAt I x₀ p.2))
      (Icc c b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
      (Icc c b ×ˢ interior (extChartAt I x₀).target) := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    rw [(isOpen_extChartAt_target (I := I) x₀).interior_eq]
    exact (extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hp.2)
  apply (hself.comp hc hm).congr
  intro p hp
  dsimp only [Function.comp_apply, chartGramOnE]
  rw [(extChartAt I x₀).left_inv (by rw [extChartAt_source]; exact hp.2)]

end DifferentialGeometry.PDE.RicciFlow
