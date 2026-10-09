import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseCrossingSeparation
import DifferentialGeometry.Topology.SphereSeparation.SourceTheorems
import DifferentialGeometry.Topology.Embedding.Sphere

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.SphereSeparation
  (SphereSides smoothSphereSidesOpenThreeSpace)

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem nonempty_sphereSides_range_coe_sphere :
    Nonempty (SphereSides (Set.range (fun x : Sphere 2 => (x : ThreeSpace)))) :=
  ⟨(smoothSphereSidesOpenThreeSpace (fun x : Sphere 2 => (x : ThreeSpace))
    (@isSmoothEmbedding_coe_sphere ThreeSpace inferInstance inferInstance 2
      (⟨by simp⟩ : Fact (Module.finrank ℝ ThreeSpace = 2 + 1)))
    (Diffeomorph.refl (𝓘(ℝ, ThreeSpace)) ThreeSpace ∞)).toSphereSides⟩

theorem sphere_separation_of_diffeomorph_euclidean
    (P : PointedRiemannianManifold.{u, 0, 0} I3)
    (ψ : Diffeomorph I3 I3 P.M ThreeSpace ∞)
    (f : Sphere 2 → P.M) (he : Manifold.IsSmoothEmbedding I2 I3 ∞ f) :
    ¬ IsPreconnected (Set.range f)ᶜ ∧
      ∀ p z : P.M, p ∉ Set.range f → z ∉ Set.range f →
        ∀ c : TransversePath p z (Set.range f),
          (c.intersection = 1 ∨ c.intersection = -1) →
            z ∉ connectedComponentIn (Set.range f)ᶜ p :=
  open_nonnegative_sphere_separation P f (smoothSphereSidesOpenThreeSpace f he ψ).toTwoSidedSeparation

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
