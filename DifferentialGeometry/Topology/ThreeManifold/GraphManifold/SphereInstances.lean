import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Sphere
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.PrimeStructureConsequences
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereSummandOccurrence

/-!
# Chapter 5 consequences with the raw graph presentation of the standard sphere

Several chapter 5 statements take a raw graph presentation of the standard three-sphere as a
hypothesis. The presentation `standardThreeSphereLiftRawGraphPresentation`, by two solid tori
glued along the Clifford torus, discharges it; this file records the resulting statements:
the prime-`M` case of the sphere-summand theorem, the prime decomposition with graph factors
under `GraphPrimeStructure`, geometrization under `GraphPrimeStructure` and the per-prime
geometric input, and the conditional sphere-summand theorems under `GraphPrimeStructure` with
either `PrimeDecompositionUnique` or the weaker `NonsphereFactorOccurrence`.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint

namespace GC.GraphManifold

universe u

theorem rawGraphPresentation_sphereSummand_of_isPrime
    {M P : ConnectedClosedOrientedManifold.{u} 3} (hM : GC.Endpoint.IsPrime M)
    (G : RawGraphPresentation (NoCuts.carrier M)) (S : GC.Topology.SphereSummand M P) :
    Nonempty (RawGraphPresentation (NoCuts.carrier P)) :=
  rawGraphPresentation_of_sphere_summand_of_isPrime
    standardThreeSphereLiftRawGraphPresentation hM G S

theorem exists_prime_decomposition_of_rawGraphPresentation_of_graphPrimeStructure
    (hS : GraphPrimeStructure.{u}) (M : ConnectedClosedOrientedManifold.{u} 3)
    (G : RawGraphPresentation (NoCuts.carrier M)) :
    ∃ D : GC.Endpoint.PrimeDecomposition M,
      ∀ i : Fin D.factors.length,
        Nonempty (RawGraphPresentation (NoCuts.carrier (D.factors.get i))) :=
  exists_prime_decomposition_of_rawGraphPresentation_of_structure hS
    standardThreeSphereLiftRawGraphPresentation M G

theorem geometrizes_of_rawGraphPresentation_of_graphPrimeStructure
    (hS : GraphPrimeStructure.{u})
    (hgeo : ∀ P : ConnectedClosedOrientedManifold.{u} 3, GC.Endpoint.IsPrime P →
      RawGraphPresentation (NoCuts.carrier P) →
        Nonempty (GC.Endpoint.GeometricDecomposition P))
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (G : RawGraphPresentation (NoCuts.carrier M)) : GC.Endpoint.Geometrizes M :=
  geometrizes_of_rawGraphPresentation_of_structure hS
    standardThreeSphereLiftRawGraphPresentation hgeo M G

theorem rawGraphPresentation_sphereSummand_of_graphPrimeStructure_of_unique
    (hS : GraphPrimeStructure.{u}) (hU : PrimeDecompositionUnique.{u})
    {M P : ConnectedClosedOrientedManifold.{u} 3}
    (G : RawGraphPresentation (NoCuts.carrier M)) (S : GC.Topology.SphereSummand M P)
    (hP : GC.Endpoint.IsPrime P) :
    Nonempty (RawGraphPresentation (NoCuts.carrier P)) :=
  rawGraphPresentation_of_sphere_summand_of_structure_of_unique hS hU
    standardThreeSphereLiftRawGraphPresentation G S hP

theorem rawGraphPresentation_sphereSummand_of_graphPrimeStructure_of_occurrence
    (hS : GraphPrimeStructure.{u}) (hO : NonsphereFactorOccurrence.{u})
    {M P : ConnectedClosedOrientedManifold.{u} 3}
    (G : RawGraphPresentation (NoCuts.carrier M)) (S : GC.Topology.SphereSummand M P)
    (hP : GC.Endpoint.IsPrime P) :
    Nonempty (RawGraphPresentation (NoCuts.carrier P)) :=
  rawGraphPresentation_of_sphere_summand_of_structure_of_occurrence hS hO
    standardThreeSphereLiftRawGraphPresentation G S hP

end GC.GraphManifold
