import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.Scalar
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity

set_option autoImplicit false

noncomputable section

open Set Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.SolutionOn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

variable (S : SolutionOn (I := I) (M := M) D) {J : Set ℝ}
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun z : ℝ × M => (⟨z.2, (S.base.metric z.1).inner z.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set M)))

include hmetric

omit [I.Boundaryless] [T2Space M] in
theorem chartGramFamilySmoothWithinOn_of_jointContMDiffOn (α : M) :
    chartGramFamilySmoothWithinOn (I := I) S.base.metric α J :=
  chartGramFamilySmoothWithinOn_of_contMDiffOn S.base.metric α
    (fun i j => chartGramMatrix_joint_contMDiffOn S.base.metric J hmetric α i j)

theorem chartRicci_contDiffOn_of_jointContMDiffOn (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E =>
        let x := (extChartAt I α).symm p.2
        S.ricciAt p.1 x (vec2 (chartBasisVecFiber (I := I) α i x)
          (chartBasisVecFiber (I := I) α j x)))
      (J ×ˢ interior (extChartAt I α).target) := by
  have hG := S.chartGramFamilySmoothWithinOn_of_jointContMDiffOn hmetric α
  have hc : ContDiffOn ℝ ∞
      (fun r : ℝ × E => chartRicciTensor (I := I) (S.base.metric r.1) α i j r.2)
      (J ×ˢ interior (extChartAt I α).target) := fun p hp =>
    chartRicciTensor_contDiffWithinAt S.base.metric α hG i j hp.1 hp.2
  refine hc.congr ?_
  intro p hp
  let x := (extChartAt I α).symm p.2
  have hxsrc : x ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target (interior_subset hp.2)
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) α :=
    (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source (I := I) α x).2 hxsrc
  have hright : extChartAt I α x = p.2 := (extChartAt I α).right_inv (interior_subset hp.2)
  change metricRicciAt (I := I) (S.base.metric p.1) x
      (vec2 (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x)) = _
  rw [metricRicciAt_apply_eq_ricciTensor,
    ricciTensor_chartBasisVec_alpha_eq (I := I) (S.base.metric p.1) α i j hxgood, hright]

theorem chartScalarDeriv_contDiffOn_of_jointContMDiffOn (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E =>
        let x := (extChartAt I α).symm p.2
        mvfderiv (I := I) (S.scalar p.1) x (chartBasisVecFiber (I := I) α j x))
      (J ×ˢ interior (extChartAt I α).target) := by
  have hG := S.chartGramFamilySmoothWithinOn_of_jointContMDiffOn hmetric α
  have hscal := scalarOnE_contDiffOn_of_chartGramFamilySmoothWithinOn S.base.metric α hG
  have hc : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      partialDeriv (E := E) j (scalarOnE (I := I) α (S.scalar p.1)) p.2)
      (J ×ˢ interior (extChartAt I α).target) := fun p hp =>
    partialDeriv_joint_contDiffWithinAt
      (fun t y => scalarOnE (I := I) α (metricScalarAt (S.base.metric t)) y) j isOpen_interior
      hp.1 hp.2 (hscal p hp)
  refine hc.congr ?_
  intro p hp
  let x := (extChartAt I α).symm p.2
  have hxsrc : x ∈ (chartAt H α).source := by
    have hxext : x ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target (interior_subset hp.2)
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hxext
  have hright : extChartAt I α x = p.2 := (extChartAt I α).right_inv (interior_subset hp.2)
  rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv]
  change mfderiv I 𝓘(ℝ, ℝ) (S.scalar p.1) x (chartBasisVecFiber (I := I) α j x) =
    partialDeriv (E := E) j (scalarOnE (I := I) α (S.scalar p.1)) p.2
  rw [← hright]
  exact DifferentialGeometry.Geometry.Operator.mfderiv_chartBasisVecFiber_of_mdifferentiableAt
    (I := I) α ((scalarSmoothOfSolution (I := I) S p.1).mdifferentiableAt (by simp))
    hxsrc (by simpa only [hright] using hp.2) j

end DifferentialGeometry.PDE.RicciFlow.SolutionOn
