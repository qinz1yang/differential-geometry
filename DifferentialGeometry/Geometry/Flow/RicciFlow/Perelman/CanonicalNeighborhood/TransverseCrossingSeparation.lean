import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseCrossingSide

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.SphereSeparation (SphereSides TwoSidedSeparation)

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]

omit [IsManifold I3 ∞ M] in
theorem not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_twoSidedSeparation
    {sphere : Set M} (d : TwoSidedSeparation sphere) :
    ¬ IsPreconnected sphereᶜ ∧
      ∀ {p z : M}, p ∉ sphere → z ∉ sphere → (c : TransversePath p z sphere) →
        (c.intersection = 1 ∨ c.intersection = -1) →
          z ∉ connectedComponentIn sphereᶜ p :=
  ⟨d.not_isPreconnected_compl, fun hp hz c hint =>
    c.not_mem_connectedComponentIn_of_intersection d hp hz hint⟩

omit [IsManifold I3 ∞ M] in
theorem not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_sphereSides
    {sphere : Set M} (d : SphereSides sphere) :
    ¬ IsPreconnected sphereᶜ ∧
      ∀ {p z : M}, p ∉ sphere → z ∉ sphere → (c : TransversePath p z sphere) →
        (c.intersection = 1 ∨ c.intersection = -1) →
          z ∉ connectedComponentIn sphereᶜ p :=
  not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_twoSidedSeparation
    d.toTwoSidedSeparation

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

omit [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] in
theorem open_nonnegative_sphere_separation
    (P : PointedRiemannianManifold.{u, 0, 0} I3)
    (f : Sphere 2 → P.M) (d : TwoSidedSeparation (Set.range f)) :
    ¬ IsPreconnected (Set.range f)ᶜ ∧
      ∀ p z : P.M, p ∉ Set.range f → z ∉ Set.range f →
        ∀ c : TransversePath p z (Set.range f),
          (c.intersection = 1 ∨ c.intersection = -1) →
            z ∉ connectedComponentIn (Set.range f)ᶜ p :=
  not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_twoSidedSeparation d

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
