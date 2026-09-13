import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EuclideanSimplexGeneratorCriterion

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Bundle Manifold Set
open scoped Simplicial Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem euclideanStandardSimplexClass_generator_of_exists_functional_eq_one
    (h : ∃ ψ : DifferentialGeometry.Topology.integralSingularHomology 2
        ({(0 : DifferentialGeometry.Topology.liftedSphereSpace.{u} 1)}ᶜ :
          Set (DifferentialGeometry.Topology.liftedSphereSpace.{u} 1)) →ₗ[ℤ] ℤ,
      ψ euclideanStandardSimplexBoundaryClass.{u} = 1) :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) :=
  euclideanStandardSimplexClass_generator_of_boundaryClass_functional_eq_one
    h.choose h.choose_spec

theorem localOrientationClass_generator_of_exists_functional_eq_one
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (o : TangentOrientationSection M) (x : M)
    (h : ∃ ψ : DifferentialGeometry.Topology.integralSingularHomology 2
        ({(0 : DifferentialGeometry.Topology.liftedSphereSpace.{u} 1)}ᶜ :
          Set (DifferentialGeometry.Topology.liftedSphereSpace.{u} 1)) →ₗ[ℤ] ℤ,
      ψ euclideanStandardSimplexBoundaryClass.{u} = 1) :
    Function.Bijective (fun z : ℤ => z • localOrientationClass o x) :=
  localOrientationClass_generator_of_euclideanStandardSimplex o x
    (euclideanStandardSimplexClass_generator_of_exists_functional_eq_one h)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
