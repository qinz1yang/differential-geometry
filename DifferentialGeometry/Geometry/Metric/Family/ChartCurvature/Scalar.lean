import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Metric.Family.Regularity.JointDifferentialOperator
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.WithinSmoothness
import DifferentialGeometry.Geometry.Curvature.Coordinates.ScalarTrace
import DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentityOffCenter

noncomputable section

open Set Bundle
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

theorem scalarOnE_contDiffOn_of_chartGramFamilySmoothWithinOn
    (g : ℝ → SmoothRiemannianMetric I M) (p : M) {J : Set ℝ}
    (hG : chartGramFamilySmoothWithinOn (I := I) g p J) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E =>
      DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := I) p (metricScalarAt (g z.1)) z.2)
      (J ×ˢ interior (extChartAt I p).target) := by
  have hs : ContDiffOn ℝ ∞ (fun z : ℝ × E =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (g z.1) p i j z.2 * chartRicciTensor (g z.1) p i j z.2)
      (J ×ˢ interior (extChartAt I p).target) := by
    intro z hz
    exact ContDiffWithinAt.sum fun i _ => ContDiffWithinAt.sum fun j _ =>
      (chartInvGramOnE_contDiffWithinAt g p hG i j hz.1 hz.2).mul
        (chartRicciTensor_contDiffWithinAt g p hG i j hz.1 hz.2)
  apply hs.congr
  intro z hz
  have hy := interior_subset hz.2
  have hx : (extChartAt I p).symm z.2 ∈ chartLeviCivitaGoodSet (I := I) p := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source]
    exact (extChartAt I p).map_target hy
  change metricScalarAt (g z.1) ((extChartAt I p).symm z.2) = _
  rw [DifferentialGeometry.PDE.RicciFlow.metricScalar_chartTrace_eq (g z.1) p hx]
  simp only [(extChartAt I p).right_inv hy]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simpa only [(extChartAt I p).right_inv hy] using
    ricciTensor_chartBasisVec_alpha_eq (g z.1) p i j hx

end DifferentialGeometry.Geometry.Curvature

end


noncomputable section
open Set Bundle Manifold
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology BigOperators
namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
  (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
    (J ×ˢ (univ : Set M)))

include hg

omit [I.Boundaryless] [T2Space M] in
private theorem gram_smooth (p : M) : chartGramFamilySmoothWithinOn g p J :=
  chartGramFamilySmoothWithinOn_of_contMDiffOn g p
    (chartGramMatrix_joint_contMDiffOn g J hg p)

private theorem scalar_partial_smooth (p : M) (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => partialDeriv (E := E) i
      (scalarOnE (I := I) p (metricScalarAt (g z.1))) z.2)
      (J ×ˢ interior (extChartAt I p).target) := by
  intro z hz
  exact partialDeriv_joint_contDiffWithinAt
    (fun t y => scalarOnE (I := I) p (metricScalarAt (g t)) y) i isOpen_interior hz.1 hz.2
    (scalarOnE_contDiffOn_of_chartGramFamilySmoothWithinOn g p (gram_smooth g hg p) z hz)

private theorem scalar_second_partial_smooth (p : M) (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => partialDeriv (E := E) i
      (partialDeriv (E := E) j (scalarOnE (I := I) p (metricScalarAt (g z.1)))) z.2)
      (J ×ˢ interior (extChartAt I p).target) := by
  intro z hz
  exact partialDeriv_joint_contDiffWithinAt
    (fun t y => partialDeriv (E := E) j (scalarOnE (I := I) p (metricScalarAt (g t))) y) i
    isOpen_interior hz.1 hz.2 (scalar_partial_smooth g hg p j z hz)

private theorem scalar_gradient_chart_continuous (p : M) :
    ContinuousOn (fun z : ℝ × E =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (g z.1) p i j z.2 *
          partialDeriv (E := E) j (scalarOnE (I := I) p (metricScalarAt (g z.1))) z.2 *
          partialDeriv (E := E) i (scalarOnE (I := I) p (metricScalarAt (g z.1))) z.2)
      (J ×ˢ interior (extChartAt I p).target) := by
  classical
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  have hinv : ContinuousOn (fun z : ℝ × E => chartInvGramOnE (g z.1) p i j z.2)
      (J ×ˢ interior (extChartAt I p).target) :=
    fun z hz => (chartInvGramOnE_contDiffWithinAt g p (gram_smooth g hg p) i j hz.1 hz.2).continuousWithinAt
  exact (hinv.mul (scalar_partial_smooth g hg p j).continuousOn).mul
    (scalar_partial_smooth g hg p i).continuousOn

private theorem scalar_laplacian_chart_continuous (p : M) :
    ContinuousOn (fun z : ℝ × E =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (g z.1) p i j z.2 *
          (partialDeriv (E := E) i (partialDeriv (E := E) j (scalarOnE (I := I) p (metricScalarAt (g z.1)))) z.2 -
            ∑ k : Fin (Module.finrank ℝ E), chartChristoffel (g z.1) p i j k z.2 *
              partialDeriv (E := E) k (scalarOnE (I := I) p (metricScalarAt (g z.1))) z.2))
      (J ×ˢ interior (extChartAt I p).target) := by
  classical
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  have hinv : ContinuousOn (fun z : ℝ × E => chartInvGramOnE (g z.1) p i j z.2)
      (J ×ˢ interior (extChartAt I p).target) :=
    fun z hz => (chartInvGramOnE_contDiffWithinAt g p (gram_smooth g hg p) i j hz.1 hz.2).continuousWithinAt
  refine hinv.mul ((scalar_second_partial_smooth g hg p i j).continuousOn.sub ?_)
  refine continuousOn_finsetSum _ fun k _ => ?_
  have hc : ContinuousOn (fun z : ℝ × E => chartChristoffel (g z.1) p i j k z.2)
      (J ×ˢ interior (extChartAt I p).target) :=
    fun z hz => (chartChristoffel_contDiffWithinAt g p (gram_smooth g hg p) i j k hz.1 hz.2).continuousWithinAt
  exact hc.mul (scalar_partial_smooth g hg p k).continuousOn

theorem scalar_gradient_norm_sq_continuousOn_of_joint_metric :
    ContinuousOn (fun p : ℝ × M => (g p.1).inner p.2
      (gradientFun (g p.1) (metricScalarAt (g p.1)) p.2)
      (gradientFun (g p.1) (metricScalarAt (g p.1)) p.2)) (J ×ˢ univ) := by
  classical
  refine continuousOn_of_locally_continuousOn ?_
  intro p hp
  let α := p.2
  let U : Set (ℝ × M) := univ ×ˢ chartLeviCivitaGoodSet (I := I) α
  have hpU : p ∈ U := ⟨mem_univ _,self_mem_chartLeviCivitaGoodSet (I := I) α⟩
  refine ⟨U,isOpen_univ.prod (chartLeviCivitaGoodSet_isOpen (I := I) α),hpU,?_⟩
  let T : Set (ℝ × M) := J ×ˢ chartLeviCivitaGoodSet (I := I) α
  have hψ : ContinuousOn (fun q : ℝ × M => (q.1,extChartAt I α q.2)) T :=
    continuous_fst.continuousOn.prodMk
      ((continuousOn_extChartAt (I := I) α).comp continuous_snd.continuousOn
        (fun q hq => chartLeviCivitaGoodSet_mem_extChartAt_source hq.2))
  have hmaps : MapsTo (fun q : ℝ × M => (q.1,extChartAt I α q.2)) T
      (J ×ˢ interior (extChartAt I α).target) := fun q hq =>
    ⟨hq.1,chartLeviCivitaGoodSet_extChartAt_mem_interior hq.2⟩
  have hlocal := (scalar_gradient_chart_continuous g hg α).comp hψ hmaps
  refine (hlocal.congr ?_).mono (fun q hq => ⟨hq.1.1,hq.2.2⟩)
  intro q hq
  simp only [Function.comp_apply]
  change (g q.1).inner q.2 (gradFun (g q.1) (metricScalarAt (g q.1)) q.2)
    (gradFun (g q.1) (metricScalarAt (g q.1)) q.2) = _
  rw [grad_norm_sq_chart (g q.1) α
    ((metricScalar_smooth (g q.1)).mdifferentiable (by simp) q.2)
    (chartLeviCivitaGoodSet_mem_chartAt_source hq.2)]
  simp only [chartInvGramOnE_def]
  rw [(extChartAt I α).left_inv (chartLeviCivitaGoodSet_mem_extChartAt_source hq.2)]

theorem scalar_laplacian_continuousOn_of_joint_metric :
    ContinuousOn (fun p : ℝ × M =>
      laplacian (LeviCivita (g p.1)) (g p.1) (metricScalarAt (g p.1)) p.2)
      (J ×ˢ univ) := by
  classical
  refine continuousOn_of_locally_continuousOn ?_
  intro p hp
  let α := p.2
  let U : Set (ℝ × M) := univ ×ˢ chartLeviCivitaGoodSet (I := I) α
  have hpU : p ∈ U := ⟨mem_univ _,self_mem_chartLeviCivitaGoodSet (I := I) α⟩
  refine ⟨U,isOpen_univ.prod (chartLeviCivitaGoodSet_isOpen (I := I) α),hpU,?_⟩
  let T : Set (ℝ × M) := J ×ˢ chartLeviCivitaGoodSet (I := I) α
  have hψ : ContinuousOn (fun q : ℝ × M => (q.1,extChartAt I α q.2)) T :=
    continuous_fst.continuousOn.prodMk
      ((continuousOn_extChartAt (I := I) α).comp continuous_snd.continuousOn
        (fun q hq => chartLeviCivitaGoodSet_mem_extChartAt_source hq.2))
  have hmaps : MapsTo (fun q : ℝ × M => (q.1,extChartAt I α q.2)) T
      (J ×ˢ interior (extChartAt I α).target) := fun q hq =>
    ⟨hq.1,chartLeviCivitaGoodSet_extChartAt_mem_interior hq.2⟩
  have hlocal := (scalar_laplacian_chart_continuous g hg α).comp hψ hmaps
  refine (hlocal.congr ?_).mono (fun q hq => ⟨hq.1.1,hq.2.2⟩)
  intro q hq
  simp only [Function.comp_apply]
  rw [laplacian_eq_chart_hessian_trace (g q.1) α (metricScalar_smooth (g q.1))
    (chartLeviCivitaGoodSet_mem_chartAt_source hq.2)]
  simp only [chartHessianTensor_def,chartIteratedPartialDeriv_def,chartInvGramOnE_def]
  rw [(extChartAt I α).left_inv (chartLeviCivitaGoodSet_mem_extChartAt_source hq.2)]

end DifferentialGeometry.Geometry.Curvature


end
