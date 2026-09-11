import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolution
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def cartesianMetricFamily (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E) :
    ℝ × E → E →L[ℝ] E →L[ℝ] ℝ := fun p => by exact (g p.1).inner p.2

theorem metricFamilySmoothOn_of_cartesian_smooth (D : RealTimeInterval)
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hg : ContDiffOn ℝ ∞ (cartesianMetricFamily g) (D.carrier ×ˢ (univ : Set E))) :
    MetricFamilySmoothOn D g := by
  have hcoeff (x : E) (v w : TangentSpace 𝓘(ℝ, E) x) :
      ContDiffOn ℝ ∞ (fun t => (g t).inner x v w) D.carrier := by
    have h := hg.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun t ht => ⟨ht, mem_univ x⟩)
    exact (h.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  refine ⟨fun x v w => (hcoeff x v w).mono D.regular_subset,
    fun x v w => (hcoeff x v w).continuousOn, ?_, ?_⟩
  · apply tensor0SFamilyContinuousOnSet_of_chartComp
      (N := fun _ => (univ : Set E)) (hN := fun _ => Filter.univ_mem)
    intro x₀ idx
    have hfull : Continuous (fun q : {t : ℝ // t ∈ D.carrier} × E =>
        cartesianMetricFamily g (q.1.val, q.2)) :=
      hg.continuousOn.comp_continuous
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        (fun q => ⟨q.1.property, mem_univ q.2⟩)
    have hpair := ((hfull.clm_apply (continuous_const (y := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx 0)))).clm_apply
      (continuous_const (y := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx 1))))
    simp only [metricTensorField_apply, TangentBundle.symmL_model_space]
    change ContinuousOn (fun q : {t : ℝ // t ∈ D.carrier} × E =>
      cartesianMetricFamily g (q.1.val, q.2) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx 0))
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx 1))) {q | q.2 ∈ (univ : Set E)}
    exact hpair.continuousOn
  · intro Idx _ frame u hframe i j
    have hf (k : Idx) : ContDiffOn ℝ ∞ (fun x : E => (frame k x : E)) u :=
      contMDiffOn_vectorSpace_iff_contDiffOn.mp (hframe.contMDiffOn k)
    have hF := hg.mono (prod_mono D.regular_subset (subset_univ u))
    have hv (k : Idx) : ContDiffOn ℝ ∞ (fun p : ℝ × E => (frame k p.2 : E))
        (D.regular ×ˢ u) :=
      (hf k).comp contDiffOn_snd (fun _ hp => hp.2)
    have h := (hF.clm_apply (hv i)).clm_apply (hv j)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact h.contMDiffOn

theorem PartialStandardSolution.metricFamilySmoothOn (S : PartialStandardSolution) :
    MetricFamilySmoothOn (lifetimeInterval S.lifetime S.lifetime_pos) S.metric := by
  exact metricFamilySmoothOn_of_cartesian_smooth _ S.metric S.smooth
end DifferentialGeometry.PDE.RicciFlow
