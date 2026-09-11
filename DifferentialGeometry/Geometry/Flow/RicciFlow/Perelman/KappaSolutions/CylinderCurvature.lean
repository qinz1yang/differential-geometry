import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderConnection
import DifferentialGeometry.Geometry.Curvature.Coordinates.ChristoffelContraction


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Tensor.Coordinates
open Bundle Manifold Set Filter
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff _root_.Topology BigOperators

private abbrev SphereModel := EuclideanSpace ℝ (Fin 2)
private abbrev CylinderModel := SphereModel × ℝ
local notation "sphereMetric" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

private local instance cylinderCurvatureSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private theorem cylinder_centeredChartTangentEquiv
    (p : SpatialNeckCylinder) (v : TangentSpace SpatialNeckCylinderModel p) :
    centeredChartTangentEquiv (I := SpatialNeckCylinderModel) p v =
      (centeredChartTangentEquiv (I := 𝓡 2) p.1 v.1, v.2) := by
  exact (trivToE_self_apply (I := SpatialNeckCylinderModel) p v).symm.trans
    ((cylinder_trivToE p p (mem_chart_source SphereModel p.1) v).trans
      (congrArg (fun w : SphereModel => (w, v.2))
        (trivToE_self_apply (I := 𝓡 2) p.1 v.1)))

private theorem sphere_contraction_differentiableAt
    (p : SpatialNeckSphere) (y : SphereModel)
    (hy : y ∈ (extChartAt (𝓡 2) p).target) (v w : SphereModel) :
    DifferentiableAt ℝ (chartChristoffelContraction sphereMetric p v w) y := by
  classical
  have hyint : y ∈ interior (extChartAt (𝓡 2) p).target := by
    rw [(isOpen_extChartAt_target (I := 𝓡 2) p).interior_eq]
    exact hy
  have hd (i j k : Fin (Module.finrank ℝ SphereModel)) :
      DifferentiableAt ℝ (chartChristoffel sphereMetric p i j k) y :=
    ((chartChristoffel_contDiffOn_interior sphereMetric p i j k).contDiffAt
      (isOpen_interior.mem_nhds hyint)).differentiableAt (by simp)
  unfold chartChristoffelContraction
  apply DifferentiableAt.fun_sum
  intro k _hk
  apply DifferentiableAt.smul_const
  exact DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ =>
    ((hd i j k).mul_const (chartCoord i v)).mul_const (chartCoord j w)


theorem shrinkingCylinder_contraction_fderiv
    (s : ℝ) (hs : s < 1) (p : SpatialNeckCylinder) (y : CylinderModel)
    (hy : y ∈ (extChartAt SpatialNeckCylinderModel p).target) (v w u : CylinderModel) :
    fderiv ℝ (chartChristoffelContraction (scalarOneShrinkingCylinderMetric s hs) p v w) y u =
      (fderiv ℝ (chartChristoffelContraction sphereMetric p.1 v.1 w.1) y.1 u.1, 0) := by
  have hyprod := hy
  rw [extChartAt_prod] at hyprod
  have hlocal : chartChristoffelContraction (scalarOneShrinkingCylinderMetric s hs) p v w =ᶠ[𝓝 y]
      (fun z : CylinderModel => (chartChristoffelContraction sphereMetric p.1 v.1 w.1 z.1, (0 : ℝ))) := by
    filter_upwards [(isOpen_extChartAt_target (I := SpatialNeckCylinderModel) p).mem_nhds hy]
      with z hz
    exact shrinkingCylinder_chartChristoffelContraction s hs p z hz v w
  have hd := ((sphere_contraction_differentiableAt p.1 y.1 hyprod.1 v.1 w.1).hasFDerivAt.comp y
    hasFDerivAt_fst).prodMk (hasFDerivAt_const (0 : ℝ) y)
  rw [hlocal.fderiv_eq]
  have heq := DFunLike.congr_fun hd.fderiv u
  simpa only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', Function.comp_def, zero_apply] using heq

private def curvatureExpression {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → E → E → E) (y v w u : E) : E :=
  fderiv ℝ (G u w) y v - fderiv ℝ (G u v) y w + G v (G u w y) y - G w (G u v y) y

private theorem native_curvature_expression
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (p : M) (X Y Z : TangentSpace I p) :
    centeredChartTangentEquiv (I := I) p (chartRiemannCLM g p X Y Z) =
      curvatureExpression (chartChristoffelContraction g p) (extChartAt I p p)
        (centeredChartTangentEquiv (I := I) p X)
        (centeredChartTangentEquiv (I := I) p Y)
        (centeredChartTangentEquiv (I := I) p Z) := by
  simpa only [curvatureExpression, ContinuousLinearEquiv.symm_apply_apply] using
    chartRiemannCLM_model_eq_contractions g p
      (centeredChartTangentEquiv (I := I) p X)
      (centeredChartTangentEquiv (I := I) p Y)
      (centeredChartTangentEquiv (I := I) p Z)

private theorem cylinder_curvature_expression
    (s : ℝ) (hs : s < 1) (p : SpatialNeckCylinder) (y : CylinderModel)
    (hy : y ∈ (extChartAt SpatialNeckCylinderModel p).target) (v w u : CylinderModel) :
    curvatureExpression (chartChristoffelContraction (scalarOneShrinkingCylinderMetric s hs) p)
        y v w u =
      (curvatureExpression (chartChristoffelContraction sphereMetric p.1) y.1 v.1 w.1 u.1, 0) := by
  simp only [curvatureExpression, shrinkingCylinder_contraction_fderiv s hs p y hy,
    shrinkingCylinder_chartChristoffelContraction s hs p y hy,
    Prod.sub_def, Prod.add_def, sub_zero, add_zero]


theorem shrinkingCylinder_chartRiemannCLM
    (s : ℝ) (hs : s < 1) (p : SpatialNeckCylinder)
    (X Y Z : TangentSpace SpatialNeckCylinderModel p) :
    chartRiemannCLM (scalarOneShrinkingCylinderMetric s hs) p X Y Z =
      (chartRiemannCLM sphereMetric p.1 X.1 Y.1 Z.1, 0) := by
  let y := extChartAt SpatialNeckCylinderModel p p
  have hy : y ∈ (extChartAt SpatialNeckCylinderModel p).target :=
    (extChartAt SpatialNeckCylinderModel p).map_source (mem_extChartAt_source p)
  have hyfst : y.1 = extChartAt (𝓡 2) p.1 p.1 := by
    dsimp only [y]
    rw [extChartAt_prod]
    rfl
  have hc := native_curvature_expression (scalarOneShrinkingCylinderMetric s hs) p X Y Z
  have hS := native_curvature_expression sphereMetric p.1 X.1 Y.1 Z.1
  have hYZ : ((centeredChartTangentEquiv (I := SpatialNeckCylinderModel) p Y,
      centeredChartTangentEquiv (I := SpatialNeckCylinderModel) p Z) : CylinderModel × CylinderModel) =
      ((centeredChartTangentEquiv (I := 𝓡 2) p.1 Y.1, Y.2),
        (centeredChartTangentEquiv (I := 𝓡 2) p.1 Z.1, Z.2)) :=
    Prod.ext (cylinder_centeredChartTangentEquiv p Y) (cylinder_centeredChartTangentEquiv p Z)
  have hcoords := congrArg₂
    (fun v : CylinderModel => fun wu : CylinderModel × CylinderModel =>
      curvatureExpression (chartChristoffelContraction (scalarOneShrinkingCylinderMetric s hs) p)
        y v wu.1 wu.2)
    (cylinder_centeredChartTangentEquiv p X)
    hYZ
  have hmodel := cylinder_curvature_expression s hs p y hy
    (centeredChartTangentEquiv (I := 𝓡 2) p.1 X.1, X.2)
    (centeredChartTangentEquiv (I := 𝓡 2) p.1 Y.1, Y.2)
    (centeredChartTangentEquiv (I := 𝓡 2) p.1 Z.1, Z.2)
  have htime := congrArg
    (fun z : SphereModel =>
      (curvatureExpression (chartChristoffelContraction sphereMetric p.1) z
        (centeredChartTangentEquiv (I := 𝓡 2) p.1 X.1)
        (centeredChartTangentEquiv (I := 𝓡 2) p.1 Y.1)
        (centeredChartTangentEquiv (I := 𝓡 2) p.1 Z.1), (0 : ℝ))) hyfst
  exact (centeredChartTangentEquiv (I := SpatialNeckCylinderModel) p).injective
    (hc.trans (hcoords.trans (hmodel.trans (htime.trans
      ((congrArg (fun v : SphereModel => (v, (0 : ℝ))) hS.symm).trans
        (cylinder_centeredChartTangentEquiv p
          (chartRiemannCLM sphereMetric p.1 X.1 Y.1 Z.1, 0)).symm)))))


theorem shrinkingCylinder_metricRm04StdAt
    (s : ℝ) (hs : s < 1) (p : SpatialNeckCylinder)
    (X Y Z W : TangentSpace SpatialNeckCylinderModel p) :
    metricRm04StandardAt (scalarOneShrinkingCylinderMetric s hs) p X Y Z W =
      (2 * (1 - s)) * metricRm04StandardAt sphereMetric p.1 X.1 Y.1 Z.1 W.1 := by
  erw [metricRm04StandardAt_eq_chartRiemannCLM, shrinkingCylinder_chartRiemannCLM,
    metricRm04StandardAt_eq_chartRiemannCLM]
  rcases p with ⟨y, z⟩
  rcases W with ⟨w, a⟩
  erw [scalarOneShrinkingCylinderMetric_inner]
  simp only [mul_zero, add_zero]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
