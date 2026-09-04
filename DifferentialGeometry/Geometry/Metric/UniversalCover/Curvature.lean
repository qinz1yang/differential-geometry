import DifferentialGeometry.Geometry.Metric.UniversalCover.Metric
import DifferentialGeometry.Geometry.Metric.UniversalCover.Coordinates
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Sections
import DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.Ricci
import DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge
import DifferentialGeometry.Geometry.Curvature.Metric.Sectional
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Finite.Defs

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

open Set Function Filter Bundle
open scoped Topology ContDiff
open DifferentialGeometry (SmoothRiemannianMetric)

open DifferentialGeometry.Integral.DivergenceTheorem (chartRiemannTensor)
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M] [PseudoEMetricSpace M] [SecondCountableTopology M]

omit [PseudoEMetricSpace M] in
omit [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M]
  [ConnectedSpace M]
  [SecondCountableTopology M] in
theorem metricRm_lifted
    (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (X Y Z W : E) :
    metricRm04StdAt
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x' X Y Z W =
      metricRm04StdAt (I := I) (M := M) g (proj (X := M) x') X Y Z W := by
  classical
  have hRModel :
      DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) x'
        (chartRiemannCLM
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x'
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm X)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm Y)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm Z)) =
        DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')
          (chartRiemannCLM (I := I) (M := M) g (proj (X := M) x')
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm X)
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm Y)
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm Z)) := by
    rw [chart_riemann_clm_model_apply, chart_riemann_clm_model_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [chartRiemannTensor_lifted (I := I) (M := M) g x' x'
      (mem_chart_source H x') i j k l]
  have hR :
      chartRiemannCLM
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x'
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm X)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm Y)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm Z) =
        chartRiemannCLM (I := I) (M := M) g (proj (X := M) x')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm X)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm Y)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm Z) := by
    apply (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
      (I := I) x').injective
    rw [hRModel]
    simp only [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_apply]
    let R : TangentSpace I x' :=
      chartRiemannCLM (I := I) (M := M) g (proj (X := M) x')
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')).symm X)
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')).symm Y)
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')).symm Z)
    change R = DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
      (I := I) x' R
    rw [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_apply]
  have hMetric :
      metricRm04StdAt
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x'
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm X)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm Y)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm Z)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm W) =
        metricRm04StdAt (I := I) (M := M) g (proj (X := M) x')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm X)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm Y)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm Z)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm W) := by
    rw [metricRm04StdAt_eq_chartRiemannCLM,
      metricRm04StdAt_eq_chartRiemannCLM, hR]
    simp only [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_symm_apply]
    let R : TangentSpace I (proj (X := M) x') :=
      chartRiemannCLM (I := I) (M := M) g (proj (X := M) x') X Y Z
    change (g.inner (proj (X := M) x')) W R =
      (g.inner (proj (X := M) x')) W R
    rfl
  simpa only [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_symm_apply]
    using hMetric

omit [PseudoEMetricSpace M]
  [NeZero (Module.finrank ℝ E)]
  [ConnectedSpace M]
  [SecondCountableTopology M]
  [SigmaCompactSpace M] in
theorem metricRm_lift_one
    (g : SmoothRiemannianMetric I M) (c : Real) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (X Y Z W : E),
      metricRm04StdAt
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) (scaleMetric (I := I) c hc g))
          x' X Y Z W =
        (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' Y Z *
            (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' X W -
          (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' X Z *
            (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' Y W := by
  intro x' X Y Z W
  rw [metricRm_lifted]
  exact metricRm_scale_one (I := I) (M := M) g (proj (X := M) x') c hc
    (hsec (proj (X := M) x')) X Y Z W

omit [PseudoEMetricSpace M]
  [ConnectedSpace M]
  [SecondCountableTopology M]
  [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannOp_lift_one
    (g : SmoothRiemannianMetric I M) (c : Real) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (X Y Z : E),
      riemannOp
          (LeviCivita (I := I)
            (liftedMetric (I := I) (scaleMetric (I := I) c hc g)))
          x' X Y Z =
        (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' Y Z • X -
          (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' X Z • Y := by
  intro x' X Y Z
  have hRm : ∀ A B C D : E,
      metricRm04StdAt
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) (scaleMetric (I := I) c hc g))
          x' A B C D =
        1 * ((liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' B C *
            (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' A D -
          (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' A C *
            (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' B D) := by
    intro A B C D
    simpa only [one_mul] using
      metricRm_lift_one (I := I) (M := M) g c hc hsec x' A B C D
  let XT : TangentSpace I x' := X
  let YT : TangentSpace I x' := Y
  let ZT : TangentSpace I x' := Z
  change riemannOp
      (LeviCivita (I := I)
        (liftedMetric (I := I) (scaleMetric (I := I) c hc g)))
      x' XT YT ZT =
    (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' YT ZT • XT -
      (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' XT ZT • YT
  simpa only [one_smul] using
    riemannOp_of_rm
      (I := I)
      (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
      (liftedMetric (I := I) (scaleMetric (I := I) c hc g)) x' 1 hRm X Y Z

omit [PseudoEMetricSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] [ConnectedSpace M] [SecondCountableTopology M] in
theorem riemannOp_lifted_natural (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (v' w' u' : E)
    (h_lifted : chartRiemannBasisIdentity
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x')
    (h_base : chartRiemannBasisIdentity (I := I) (M := M) g (proj (X := M) x')) :
    riemannOp (LeviCivita (I := I) (liftedMetric (I := I) g)) x' v' w' u' =
      riemannOp (LeviCivita (I := I) g) (proj x') v' w' u' := by
  classical
  have hRModel :
      DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) x'
        (chartRiemannCLM
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x'
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm v')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm w')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm u')) =
        DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')
          (chartRiemannCLM (I := I) (M := M) g (proj (X := M) x')
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm v')
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm w')
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm u')) := by
    rw [chart_riemann_clm_model_apply, chart_riemann_clm_model_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [chartRiemannTensor_lifted (I := I) (M := M) g x' x'
      (mem_chart_source H x') i j k l]
  have hModel :
      DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) x'
        (riemannOp (LeviCivita (I := I) (liftedMetric (I := I) g)) x'
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm v')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm w')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm u')) =
        DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')
          (riemannOp (LeviCivita (I := I) g) (proj (X := M) x')
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm v')
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm w')
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm u')) := by
    rw [riemannOp_eq_chartRiemannCLM_apply_of_basis_identity
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x' h_lifted,
        riemannOp_eq_chartRiemannCLM_apply_of_basis_identity
          (I := I) (M := M) g (proj (X := M) x') h_base]
    exact hRModel
  have hR :
      riemannOp (LeviCivita (I := I) (liftedMetric (I := I) g)) x'
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm v')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm w')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm u') =
        riemannOp (LeviCivita (I := I) g) (proj (X := M) x')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm v')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm w')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm u') := by
    apply (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
      (I := I) x').injective
    rw [hModel]
    simp only [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_apply]
    let R : TangentSpace I x' :=
      riemannOp (LeviCivita (I := I) g) (proj (X := M) x')
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')).symm v')
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')).symm w')
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')).symm u')
    change R = DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
      (I := I) x' R
    rw [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_apply]
  simpa only [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_symm_apply]
    using hR

omit [PseudoEMetricSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] [ConnectedSpace M] [SecondCountableTopology M] in
theorem ricciTensor_lifted_natural (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (v' w' : E)
    (h_lifted : chartRiemannBasisIdentity
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x')
    (h_base : chartRiemannBasisIdentity (I := I) (M := M) g (proj (X := M) x')) :
    ricciTensor (I := I) (liftedMetric (I := I) g) x' v' w' =
      ricciTensor (I := I) g (proj x') v' w' := by
  classical
  rw [ricciTensor_apply_basisSum
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x' v' w',
      ricciTensor_apply_basisSum (I := I) (M := M) g (proj (X := M) x') v' w']
  refine Finset.sum_congr rfl ?_
  intro i _
  have hRiem :
      riemannOp (cov := LeviCivita (I := I) (liftedMetric (I := I) g)) x'
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) v' w' =
        riemannOp (cov := LeviCivita (I := I) g) (proj (X := M) x')
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) v' w' :=
    riemannOp_lifted_natural (I := I) (M := M) g x'
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) v' w' h_lifted h_base
  simp only [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis_repr,
    DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis_apply,
    DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply,
    DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_symm_apply,
    tangentSpaceModelContinuousLinearEquiv_apply]
  rw [hRiem]

omit [PseudoEMetricSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] [ConnectedSpace M] [SecondCountableTopology M] in
theorem ricciBoundedBelow_liftedMetric_of_base
    {g : SmoothRiemannianMetric I M} {κ : ℝ}
    (hRic : RicciBoundedBelow (I := I) g κ)
    (h_lifted_all : ∀ x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M,
        chartRiemannBasisIdentity
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x')
    (h_base_all : ∀ x : M, chartRiemannBasisIdentity (I := I) (M := M) g x) :
    RicciBoundedBelow (I := I) (liftedMetric (I := I) g) κ := by
  intro x' v'
  set x : M := proj x' with hx_def
  have h_inner :
      (liftedMetric (I := I) g).inner x' v' v' = g.inner x v' v' := by
    exact (liftedMetric_inner_eq (I := I) g x' v' v').symm
  have h_ric :
      ricciTensor (I := I) (liftedMetric (I := I) g) x' v' v' =
        ricciTensor (I := I) g x v' v' :=
    ricciTensor_lifted_natural (I := I) g x' v' v'
      (h_lifted_all x') (h_base_all (proj (X := M) x'))
  rw [h_inner, h_ric]
  exact hRic x v'

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
