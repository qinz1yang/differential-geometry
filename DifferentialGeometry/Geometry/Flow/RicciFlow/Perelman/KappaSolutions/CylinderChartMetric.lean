import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Product
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderMetric
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartSection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Metric
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set Filter
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open scoped Manifold ContDiff _root_.Topology BigOperators

private abbrev SphereModel := EuclideanSpace ℝ (Fin 2)
private abbrev CylinderModel := SphereModel × ℝ

private local instance cylinderSphereOneNormedGroup : NormedAddCommGroup (SphereModel →L[ℝ] ℝ) := inferInstance
private local instance cylinderSphereOneNormedSpace : NormedSpace ℝ (SphereModel →L[ℝ] ℝ) := inferInstance
private local instance cylinderSphereTwoNormedGroup : NormedAddCommGroup (SphereModel →L[ℝ] SphereModel →L[ℝ] ℝ) := inferInstance
private local instance cylinderSphereTwoNormedSpace : NormedSpace ℝ (SphereModel →L[ℝ] SphereModel →L[ℝ] ℝ) := inferInstance
private local instance cylinderOneNormedGroup : NormedAddCommGroup (CylinderModel →L[ℝ] ℝ) := inferInstance
private local instance cylinderOneNormedSpace : NormedSpace ℝ (CylinderModel →L[ℝ] ℝ) := inferInstance
private local instance cylinderTwoNormedGroup : NormedAddCommGroup (CylinderModel →L[ℝ] CylinderModel →L[ℝ] ℝ) := inferInstance
private local instance cylinderTwoNormedSpace : NormedSpace ℝ (CylinderModel →L[ℝ] CylinderModel →L[ℝ] ℝ) := inferInstance

private local instance cylinderChartSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private theorem cylinder_chart_source (p x : SpatialNeckCylinder)
    (hx : x.1 ∈ (chartAt SphereModel p.1).source) :
    x ∈ (chartAt (ModelProd SphereModel ℝ) p).source := by
  exact ⟨hx, mem_univ x.2⟩

private theorem cylinder_mfderiv_prodMap_space (x : SpatialNeckCylinder)
    (f : SpatialNeckSphere → SphereModel)
    (hf : MDifferentiableAt (𝓡 2) 𝓘(ℝ, SphereModel) f x.1) :
    mfderiv SpatialNeckCylinderModel 𝓘(ℝ, CylinderModel) (Prod.map f id) x =
      (mfderiv (𝓡 2) 𝓘(ℝ, SphereModel) f x.1).prodMap
        (ContinuousLinearMap.id ℝ ℝ) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  rw [mfderiv_prodMap hf mdifferentiableAt_id, mfderiv_id]
  rfl


theorem cylinder_trivToE (p x : SpatialNeckCylinder)
    (hx : x.1 ∈ (chartAt SphereModel p.1).source)
    (v : TangentSpace SpatialNeckCylinderModel x) :
    trivToE (I := SpatialNeckCylinderModel) p x v =
      (trivToE (I := 𝓡 2) p.1 x.1 v.1, v.2) := by
  have hprod := cylinder_chart_source p x hx
  have hfun : (extChartAt SpatialNeckCylinderModel p : SpatialNeckCylinder → CylinderModel) =
      Prod.map (extChartAt (𝓡 2) p.1) id := by
    rw [extChartAt_prod]
    rfl
  rw [trivToE, TangentBundle.continuousLinearMapAt_trivializationAt hprod, hfun]
  rw [cylinder_mfderiv_prodMap_space x _ (mdifferentiableAt_extChartAt hx)]
  rw [trivToE, TangentBundle.continuousLinearMapAt_trivializationAt hx]
  rfl


theorem cylinder_trivFromE (p x : SpatialNeckCylinder)
    (hx : x.1 ∈ (chartAt SphereModel p.1).source) (v : CylinderModel) :
    trivFromE (I := SpatialNeckCylinderModel) p x v =
      (trivFromE (I := 𝓡 2) p.1 x.1 v.1, v.2) := by
  have hprod : x ∈ (trivializationAt CylinderModel
      (TangentSpace SpatialNeckCylinderModel) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact cylinder_chart_source p x hx
  have hsphere : x.1 ∈ (trivializationAt SphereModel (TangentSpace (𝓡 2)) p.1).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hx
  let w := trivFromE (I := SpatialNeckCylinderModel) p x v
  have hpair : (trivToE (I := 𝓡 2) p.1 x.1 w.1, w.2) = v :=
    (cylinder_trivToE p x hx w).symm.trans
      (trivToE_trivFromE (I := SpatialNeckCylinderModel) p hprod v)
  have hsecond := congrArg (fun z : CylinderModel => z.2) hpair
  change (w : CylinderModel) = (trivFromE (I := 𝓡 2) p.1 x.1 v.1, v.2)
  apply Prod.ext
  · have hh := congrArg (trivFromE (I := 𝓡 2) p.1 x.1) (congrArg Prod.fst hpair)
    exact (trivFromE_trivToE (I := 𝓡 2) p.1 hsphere w.1).symm.trans hh
  · exact hsecond


theorem shrinkingCylinder_chartGramBilin (s : ℝ) (hs : s < 1)
    (p x : SpatialNeckCylinder) (hx : x.1 ∈ (chartAt SphereModel p.1).source) :
    chartGramBilin (scalarOneShrinkingCylinderMetric s hs) p x =
      lineProductMetricForm
        (chartGramBilin (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) p.1 x.1)
        (2 * (1 - s)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  calc
    _ = (scalarOneShrinkingCylinderMetric s hs).inner x
        (trivFromE (I := SpatialNeckCylinderModel) p x v)
        (trivFromE (I := SpatialNeckCylinderModel) p x w) := by
      simp only [chartGramBilin_eq_innerJinv, modelInnerAt_apply, chartJinv_apply,
        ContinuousLinearEquiv.symm_apply_apply]
    _ = 2 * (1 - s) *
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x.1
          (trivFromE (I := 𝓡 2) p.1 x.1 v.1) (trivFromE (I := 𝓡 2) p.1 x.1 w.1) +
        v.2 * w.2 := by
      rw [cylinder_trivFromE p x hx v, cylinder_trivFromE p x hx w]
      exact scalarOneShrinkingCylinderMetric_inner s hs x.1 x.2 _ _ v.2 w.2
    _ = _ := by
      simp only [lineProductMetricForm_apply, chartGramBilin_eq_innerJinv,
        modelInnerAt_apply, chartJinv_apply, ContinuousLinearEquiv.symm_apply_apply]


theorem shrinkingCylinder_chartGramBilin_in_coordinates (s : ℝ) (hs : s < 1)
    (p : SpatialNeckCylinder) (y : CylinderModel)
    (hy : y ∈ (extChartAt SpatialNeckCylinderModel p).target) :
    chartGramBilin (scalarOneShrinkingCylinderMetric s hs) p
        ((extChartAt SpatialNeckCylinderModel p).symm y) =
      lineProductMetricForm
        (chartGramBilin (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
          p.1 ((extChartAt (𝓡 2) p.1).symm y.1)) (2 * (1 - s)) := by
  have hsource := (extChartAt SpatialNeckCylinderModel p).map_target hy
  rw [extChartAt_source] at hsource
  have hx : ((extChartAt SpatialNeckCylinderModel p).symm y).1 ∈
      (chartAt SphereModel p.1).source := hsource.1
  have hform := shrinkingCylinder_chartGramBilin s hs p _ hx
  have hfst : ((extChartAt SpatialNeckCylinderModel p).symm y).1 =
      (extChartAt (𝓡 2) p.1).symm y.1 := by
    rw [extChartAt_prod]
    rfl
  rw [hfst] at hform
  exact hform

private theorem chartGramBilin_coordinates_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (p : M) {y : E}
    (hy : y ∈ interior (extChartAt I p).target) :
    DifferentiableAt ℝ (fun u => chartGramBilin g p ((extChartAt I p).symm u)) y := by
  classical
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  change DifferentiableAt ℝ (fun u =>
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      chartGramOnE g p i j u • (chartCoordCLM E i).smulRight (chartCoordCLM E j)) y
  refine DifferentiableAt.fun_sum (fun i _ => ?_)
  refine DifferentiableAt.fun_sum (fun j _ => ?_)
  exact (chartGramOnE_differentiableAt_int g p i j hy).smul_const _


theorem shrinkingCylinder_chartGramBilin_hasFDerivAt (s : ℝ) (hs : s < 1)
    (p : SpatialNeckCylinder) (y : CylinderModel)
    (hy : y ∈ (extChartAt SpatialNeckCylinderModel p).target) :
    HasFDerivAt (fun u => chartGramBilin (scalarOneShrinkingCylinderMetric s hs) p
        ((extChartAt SpatialNeckCylinderModel p).symm u))
      (lineProductMetricDerivative
        (fderiv ℝ (fun u => chartGramBilin
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) p.1
          ((extChartAt (𝓡 2) p.1).symm u)) y.1) (2 * (1 - s))) y := by
  have hyprod := hy
  rw [extChartAt_prod] at hyprod
  have hysphere : y.1 ∈ interior (extChartAt (𝓡 2) p.1).target := by
    rw [(isOpen_extChartAt_target (I := 𝓡 2) p.1).interior_eq]
    exact hyprod.1
  have hB := chartGramBilin_coordinates_differentiableAt
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) p.1 hysphere
  apply (hasFDerivAt_lineProductMetricForm (x := y) hB.hasFDerivAt (2 * (1 - s))).congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_target (I := SpatialNeckCylinderModel) p).mem_nhds hy]
    with u hu
  exact shrinkingCylinder_chartGramBilin_in_coordinates s hs p u hu


theorem shrinkingCylinder_chartGramBilin_fderiv (s : ℝ) (hs : s < 1)
    (p : SpatialNeckCylinder) (y : CylinderModel)
    (hy : y ∈ (extChartAt SpatialNeckCylinderModel p).target) :
    fderiv ℝ (fun u => chartGramBilin (scalarOneShrinkingCylinderMetric s hs) p
        ((extChartAt SpatialNeckCylinderModel p).symm u)) y =
      lineProductMetricDerivative
        (fderiv ℝ (fun u => chartGramBilin
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) p.1
          ((extChartAt (𝓡 2) p.1).symm u)) y.1) (2 * (1 - s)) :=
  (shrinkingCylinder_chartGramBilin_hasFDerivAt s hs p y hy).fderiv

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
