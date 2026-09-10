import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Covering.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance upstreamSurfaceCoverSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

local instance upstreamSurfaceCoverC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

theorem complete_surface_constant_scalar_round_cover
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hscalar : ∀ x : M, metricScalarAt (I := I) g x = sigma) :
    ∃ pi : SphereTwo → M,
      IsLocalDiffeomorph (𝓡 2) I ∞ pi ∧ IsCoveringMap pi ∧ Function.Surjective pi ∧
      (∀ (x : SphereTwo) (v w : TangentSpace (𝓡 2) x),
        g.inner (pi x) (mfderiv (𝓡 2) I pi x v) (mfderiv (𝓡 2) I pi x w) =
          (2 / sigma) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
            x v w) ∧
      (Function.Injective pi ∨
        ∀ x y : SphereTwo, pi x = pi y ↔ y = x ∨ y = -x) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
