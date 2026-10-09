import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.PrimeStructure
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereInstances

/-!
# Chapter 5 endpoints from the normalization

Endpoint A of survey X31 §5 (review 19 §8). The prime structure `graphPrimeStructure_of_normalize`
is passed to the existing consumers of `SphereInstances.lean`, whose signatures are unchanged:
`endpoint_prime_decomposition` gives a prime decomposition of every closed `M` with a raw graph
presentation whose factors all have raw presentations (the statement of
`exists_prime_decomposition_of_rawGraphPresentation` in `Refinement.lean`, now without the
sphere-splitting admissions), and `endpoint_geometrizes` keeps the per-prime geometric input
`hgeo` of the geometric consumer. `sphereSummand_of_normalize_of_occurrence` is only the
conditional wiring of Endpoint B: it keeps the occurrence input `hO` and does not replace the
admission `rawGraphPresentation_of_sphere_summand`.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert

namespace GC.GraphManifold

universe u

theorem endpoint_prime_decomposition
    (hM2 : MoveSplitTerminalRaw.{u}) (hE : ElementarizeOnSubCollar.{u})
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (M : ConnectedClosedOrientedManifold.{u} 3) (G : RawGraphPresentation (NoCuts.carrier M)) :
    ∃ D : PrimeDecomposition M,
      ∀ i : Fin D.factors.length,
        Nonempty (RawGraphPresentation (NoCuts.carrier (D.factors.get i))) :=
  exists_prime_decomposition_of_rawGraphPresentation_of_graphPrimeStructure
    (graphPrimeStructure_of_normalize hM2 hE hfin hnon) M G

theorem endpoint_geometrizes
    (hM2 : MoveSplitTerminalRaw.{u}) (hE : ElementarizeOnSubCollar.{u})
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (hgeo : ∀ P : ConnectedClosedOrientedManifold.{u} 3, IsPrime P →
      RawGraphPresentation (NoCuts.carrier P) → Nonempty (GeometricDecomposition P))
    (M : ConnectedClosedOrientedManifold.{u} 3) (G : RawGraphPresentation (NoCuts.carrier M)) :
    Geometrizes M :=
  geometrizes_of_rawGraphPresentation_of_graphPrimeStructure
    (graphPrimeStructure_of_normalize hM2 hE hfin hnon) hgeo M G

theorem sphereSummand_of_normalize_of_occurrence
    (hM2 : MoveSplitTerminalRaw.{u}) (hE : ElementarizeOnSubCollar.{u})
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (hO : NonsphereFactorOccurrence.{u}) {M P : ConnectedClosedOrientedManifold.{u} 3}
    (G : RawGraphPresentation (NoCuts.carrier M)) (S : GC.Topology.SphereSummand M P)
    (hP : IsPrime P) : Nonempty (RawGraphPresentation (NoCuts.carrier P)) :=
  rawGraphPresentation_sphereSummand_of_graphPrimeStructure_of_occurrence
    (graphPrimeStructure_of_normalize hM2 hE hfin hnon) hO G S hP

end GC.GraphManifold
