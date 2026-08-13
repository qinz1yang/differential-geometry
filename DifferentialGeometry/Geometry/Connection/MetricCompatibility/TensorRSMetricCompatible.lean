import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorMetricCompatible
import DifferentialGeometry.Geometry.Metric.PointwiseInner.MetricLowering
open DifferentialGeometry.Geometry.Curvature


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix


namespace DifferentialGeometry
namespace Geometry
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.TensorMetricLowering
open DifferentialGeometry.Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

def liftedTensorSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯) :
    Π y : M, Tensor0SSpace (r + s) I y :=
  fun y => Tensor0SSpace.ofModel
    (lowerAllUpperIndices (I := I) (M := M) g r s y (TensorRSSpace.toModel (S y)))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [T2Space M]
    [BoundarylessManifold I M] in
@[simp]
lemma liftedTensorSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (y : M) :
    liftedTensorSection (I := I) (M := M) g r s S y =
      Tensor0SSpace.ofModel
        (lowerAllUpperIndices (I := I) (M := M) g r s y
          (TensorRSSpace.toModel (S y))) := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [T2Space M]
    [BoundarylessManifold I M] in
@[simp]
lemma toModel_liftedTensorSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (y : M) :
    Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g r s S y) =
      lowerAllUpperIndices (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (S y)) := by
  rw [liftedTensorSection_apply, Tensor0SSpace.toModel_ofModel]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [T2Space M]
    [BoundarylessManifold I M] in
lemma liftedTensorSection_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (r + s) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (r + s) ℝ E)
        (E := fun z : M => Tensor0SSpace (r + s) I z) y
        (liftedTensorSection (I := I) (M := M) g r s S y)) :=
  contMDiff_lifted_section (I := I) (M := M) g r s S

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [T2Space M]
    [BoundarylessManifold I M] in
lemma liftedTensorSection_mdiffAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) :
    TensorSectionMDiffAt (I := I) (r + s)
      (liftedTensorSection (I := I) (M := M) g r s S) x :=
  ((liftedTensorSection_contMDiff (I := I) (M := M) g r s S) x).mdifferentiableAt
    (by simp)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [T2Space M]
    [BoundarylessManifold I M] in
lemma tensorInnerPointwise_eq_liftedTensorSection_inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (y : M) :
    tensorInnerPointwise (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y)) =
      covariantTensorInnerPointwise (I := I) (M := M) (r + s) g y
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g r s W y))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s S y)) := by
  rw [toModel_liftedTensorSection, toModel_liftedTensorSection]
  rfl

def loweredCovDerivAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) (v : TangentSpace I x) :
    Tensor0SSpace (r + s) I x :=
  tensor0SCovariantDerivative I M (r + s) (LeviCivita (I := I) g)
    (liftedTensorSection (I := I) (M := M) g r s S) x v

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp]
lemma loweredCovDerivAt_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) (v : TangentSpace I x) :
    loweredCovDerivAt (I := I) (M := M) g r s S x v =
      tensor0SCovariantDerivative I M (r + s) (LeviCivita (I := I) g)
        (liftedTensorSection (I := I) (M := M) g r s S) x v := rfl

open DifferentialGeometry.Tensor0SNabla in
omit [CompleteSpace E] in
theorem tensorInnerPointwise_hasMFDerivAt_metricCompatible
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, ℝ)
        (fun y : M => tensorInnerPointwise (I := I) (M := M) g r s y
          (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y))) x v =
      covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g r s W x v))
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s S x))
        + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s W x))
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g r s S x v)) := by
  have hfun : (fun y : M => tensorInnerPointwise (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y))) =
      fun y : M => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g y
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g r s W y))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s S y)) := by
    funext y
    exact tensorInnerPointwise_eq_liftedTensorSection_inner
      (I := I) (M := M) g r s W S y
  rw [hfun]
  exact tensorInnerPointwise_0s_mfderiv_metricCompatible
    (I := I) (M := M) g (r + s)
    (liftedTensorSection (I := I) (M := M) g r s W)
    (liftedTensorSection (I := I) (M := M) g r s S)
    (liftedTensorSection_mdiffAt (I := I) (M := M) g r s W x)
    (liftedTensorSection_mdiffAt (I := I) (M := M) g r s S x) v

open DifferentialGeometry.Tensor0SNabla in
omit [CompleteSpace E] in
theorem tensorInnerPointwise_hasMFDerivAt_metricCompatible'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) :
    HasMFDerivAt I 𝓘(ℝ, ℝ)
      (fun y : M => tensorInnerPointwise (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y))) x
      (tensorMetricCompatDiff (I := I) (M := M) g (r + s)
        (liftedTensorSection (I := I) (M := M) g r s W)
        (liftedTensorSection (I := I) (M := M) g r s S) x) := by
  have hfun : (fun y : M => tensorInnerPointwise (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y))) =
      fun y : M => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g y
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g r s W y))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s S y)) := by
    funext y
    exact tensorInnerPointwise_eq_liftedTensorSection_inner
      (I := I) (M := M) g r s W S y
  rw [hfun]
  exact tensorInnerPointwise_0s_hasMFDerivAt_metricCompatible_aux
    (I := I) (M := M) g (r + s)
    (liftedTensorSection (I := I) (M := M) g r s W)
    (liftedTensorSection (I := I) (M := M) g r s S)
    (liftedTensorSection_mdiffAt (I := I) (M := M) g r s W x)
    (liftedTensorSection_mdiffAt (I := I) (M := M) g r s S x)

end Connection
end Geometry
end DifferentialGeometry

end
