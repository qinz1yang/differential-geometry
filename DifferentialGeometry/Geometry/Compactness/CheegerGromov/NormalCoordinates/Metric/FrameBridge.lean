import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Bounds
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.Coordinates
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.Scaling

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

omit [NeZero (Module.finrank Real E)] in
theorem NormalCoordMetricEquivOn.metric_inner_bounds
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) {U : Set E}
    (h : NormalCoordMetricEquivOn (I := I) Y x U) (h0 : 0 ∈ U) (v : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (1 / 2 : Real) * ‖v‖ ^ 2 ≤ Y.metric.inner x v v ∧
      Y.metric.inner x v v ≤ 2 * ‖v‖ ^ 2 := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [← normal_coord_metric_zero (I := I) Y x]
  exact h 0 h0 v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem metric_inner_eq_innerSL_of_eq_on_normalCoordMetric_intrinsicFrameMetric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (U : Set E) (h0 : (0 : E) ∈ U)
    (hcomplete : MetricComplete (I := I) Y) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M :=
      MetricComplete.complete (I := I) Y hcomplete
    (hEnorm : ∀ (y : Y.M) (w : TangentSpace I y),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner y w w))) →
    Set.EqOn (normalCoordMetric (I := I) Y x)
        (intrinsicFrameMetric (I := I) Y.metric hEnorm x) U →
      Y.metric.inner x = (innerSL Real : E →L[Real] E →L[Real] Real) := by
  intro hEnorm h
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M :=
    MetricComplete.complete (I := I) Y hcomplete
  have h0' : normalCoordMetric (I := I) Y x 0 =
      intrinsicFrameMetric (I := I) Y.metric hEnorm x 0 := h h0
  rw [← normal_coord_metric_zero (I := I) Y x, h0',
    intrinsicFrameMetric_zero (I := I) Y.metric hEnorm x]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrinsicFramedExp_eq_expMapDiffeo_normalFrame
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (hcomplete : MetricComplete (I := I) Y) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M :=
      MetricComplete.complete (I := I) Y hcomplete
    (hEnorm : ∀ (y : Y.M) (w : TangentSpace I y),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner y w w))) →
    ∀ {z : E}, z ∈ (intrinsicFrameDiffeo (I := I) Y.metric hEnorm x).source →
      intrinsicFramedExp (I := I) Y.metric hEnorm x z =
        expMapDiffeo (I := I) Y.metric x
          (tangentSpaceModelContinuousLinearEquiv (I := I) x
            (normalFrame (I := I) Y.metric x z)) := by
  intro hEnorm z hz
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M :=
    MetricComplete.complete (I := I) Y hcomplete
  exact (intrinsicFramedExp_eq_framedExpDiffeo (I := I) Y.metric hEnorm x hz).trans
    (framedExp_apply (I := I) Y.metric x z)

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E] in
theorem scaledEuclideanMetric_inner_zero_apply (v w : E) :
    (scaleMetric (I := 𝓘(Real, E)) 4 (by norm_num)
        (euclideanMetric (E := E))).inner 0 v w = 4 * inner Real v w := by
  change (scaleMetric (I := 𝓘(Real, E)) 4 (by norm_num)
      (euclideanMetric (E := E))).inner 0
        (show TangentSpace 𝓘(Real, E) (0 : E) from v)
        (show TangentSpace 𝓘(Real, E) (0 : E) from w) = 4 * inner Real v w
  rw [scaleMetric_inner, euclideanMetric_inner]
  rfl

omit [CompleteSpace E] in
theorem exists_scaledEuclideanMetric_inner_not_le :
    ∃ v : E, ¬ ((1 / 2 : Real) * ‖v‖ ^ 2 ≤
          (scaleMetric (I := 𝓘(Real, E)) 4 (by norm_num)
            (euclideanMetric (E := E))).inner 0 v v ∧
        (scaleMetric (I := 𝓘(Real, E)) 4 (by norm_num)
            (euclideanMetric (E := E))).inner 0 v v ≤ 2 * ‖v‖ ^ 2) := by
  have hne : Module.finrank Real E ≠ 0 := NeZero.ne (Module.finrank Real E)
  refine ⟨stdOrthonormalBasis Real E ⟨0, Nat.pos_of_ne_zero hne⟩, ?_⟩
  rw [scaledEuclideanMetric_inner_zero_apply,
    real_inner_self_eq_norm_sq,
    (stdOrthonormalBasis Real E).orthonormal.norm_eq_one ⟨0, Nat.pos_of_ne_zero hne⟩]
  norm_num

end CheegerGromovCompactness
end DifferentialGeometry
