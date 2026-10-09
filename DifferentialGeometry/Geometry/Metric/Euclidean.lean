import DifferentialGeometry.Geometry.Metric.Completeness
import Mathlib.Geometry.Manifold.Riemannian.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]

noncomputable def euclideanMetric : SmoothRiemannianMetric 𝓘(Real, E) E where
  inner := (riemannianMetricVectorSpace E).inner
  symm := (riemannianMetricVectorSpace E).symm
  pos := (riemannianMetricVectorSpace E).pos
  isVonNBounded := (riemannianMetricVectorSpace E).isVonNBounded
  contMDiff := (riemannianMetricVectorSpace E).contMDiff.of_le le_top

omit [FiniteDimensional Real E] in
@[simp] theorem euclideanMetric_inner
    (x : E) (v w : TangentSpace 𝓘(Real, E) x) :
    euclideanMetric.inner x v w = inner Real v w := by
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem euclideanMetric_complete :
    RiemannianMetricComplete (I := 𝓘(Real, E)) (euclideanMetric (E := E)) := by
  let sourceEMetric : EMetricSpace E := inferInstance
  let sourceComplete :
      @CompleteSpace E sourceEMetric.toPseudoEMetricSpace.toUniformSpace :=
    inferInstance
  let sourceEdist : E → E → ENNReal := fun x y => edist x y
  have hsource : ∀ x y : E,
      sourceEdist x y = riemannianEDist 𝓘(Real, E) x y := by
    intro x y
    exact IsRiemannianManifold.out (I := 𝓘(Real, E)) x y
  refine ⟨?_⟩
  let : RiemannianBundle
      (fun x : E => TangentSpace 𝓘(Real, E) x) :=
    ⟨euclideanMetric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun x : E => TangentSpace 𝓘(Real, E) x) :=
    ⟨euclideanMetric.inner,
      euclideanMetric.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  have hed : ∀ x y : E, edist x y = sourceEdist x y := by
    intro x y
    rw [IsRiemannianManifold.out (I := 𝓘(Real, E)) x y]
    exact (hsource x y).symm
  refine EMetric.complete_of_cauchySeq_tendsto (γ := E) fun s hs => ?_
  have hsTarget : ∀ ε > (0 : ENNReal), ∃ N,
      ∀ m, N ≤ m → ∀ n, N ≤ n → edist (s m) (s n) < ε :=
    EMetric.cauchySeq_iff.mp hs
  change ∃ x, Filter.Tendsto s Filter.atTop (𝓝 x)
  let : EMetricSpace E := sourceEMetric
  let : CompleteSpace E := sourceComplete
  have hsSource : CauchySeq s := EMetric.cauchySeq_iff.mpr (by
    intro ε hε
    obtain ⟨N, hN⟩ := hsTarget ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    change sourceEdist (s m) (s n) < ε
    rw [← hed]
    exact hN m hm n hn)
  exact cauchySeq_tendsto_of_complete hsSource

end DifferentialGeometry
