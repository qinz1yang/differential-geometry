import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC41RowSFRApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereE2E
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0LoopL1E2E
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SingletonE2E

/-!
# Inhabitants of FC42 run on the FC41 row `fc41_row_SFR`

Lane S-FC41 (suffix `_SFR`), group G2. The consumers of `fc41_row_SFR` are applied to the actual
certificates of the tree, so that the row's step packets are exercised on real data:

* the S³ strong certificate (two zero balls, one slim `S² × I`, two handles, one sphere seam):
  `fc41_row_sphere_raw_SFR` runs the μ-recursion from the row (sphere step S5/N3, capped
  components, A3/A4), `fc41_row_sphere_closedGeometric_SFR` the closed threshold form;
* the one-ball / one-handle loop certificate of the same S³ (`μ = 0`, so the torus assembly with L1
  of conjunct 17): `fc41_row_loop_raw_SFR`;
* the two TRIVIAL one-vertex fixtures of X136 (`configurationW b`, `b : Bool`: one vertex, no faces,
  no handles, no seams, i.e. every family of the certificate except the vertex family is empty,
  `configurationCounts`): `fc41_row_configuration_closedGeometric_SFR`;
* the closed zero fixture (`zeroW`, one closed zero ball): its vertex is closed zero, so the
  row's closed `sec ≥ 0` disjunction is the only route: `fc41_row_zero_closedGeometric_SFR`.

No consumer here assumes anything about the certificates beyond what their producers proved.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

open FC39P0 FC39P0.X136 FC39P0.X137

/-- **The S³ certificate, FC42 recursion from the row**: a raw presentation of `S³`. -/
theorem fc41_row_sphere_raw_SFR : Nonempty (RawGraphPresentation sphereW) :=
  nonempty_rawGraphPresentation_of_fc41_row_SFR.{0} sphereW sphereStrongCertificate.1
    sphereStrongCertificate_vertex_ne_closedZero_E2E sphereStrongCertificate.2

/-- **The S³ certificate, closed threshold form from the row.** -/
theorem fc41_row_sphere_closedGeometric_SFR :
    Nonempty (RawGraphPresentation sphereW) ∨
      (sphereW.model.boundary sphereW.Carrier = ∅ ∧
        ∃ G : GC.Geometry.GeometricStructure sphereW.model sphereW.Carrier,
          G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) :=
  exists_rawGraphPresentation_or_closedGeometric_of_fc41_row_SFR.{0} sphereW
    sphereStrongCertificate.1 sphereStrongCertificate.2

/-- **The loop certificate (`μ = 0`, torus assembly with L1), FC42 recursion from the row.** -/
theorem fc41_row_loop_raw_SFR :
    Nonempty (RawGraphPresentation (NoCuts.carrier standardThreeSphereLift.{0})) :=
  nonempty_rawGraphPresentation_of_fc41_row_SFR.{0} (NoCuts.carrier standardThreeSphereLift.{0})
    loopActualCertificate vertex_ne_closedZero loopActualStrongCertificate.property

/-- **The trivial one-vertex fixtures, closed threshold form from the row.** -/
theorem fc41_row_configuration_closedGeometric_SFR (b : Bool) :
    Nonempty (RawGraphPresentation (configurationW b)) ∨
      ((configurationW b).model.boundary (configurationW b).Carrier = ∅ ∧
        ∃ G : GC.Geometry.GeometricStructure (configurationW b).model
            (configurationW b).Carrier,
          G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) :=
  exists_rawGraphPresentation_or_closedGeometric_of_fc41_row_SFR.{0} (configurationW b)
    (configurationStrong b).1 (configurationStrong b).2

/-- **The closed zero fixture, closed threshold form from the row.** -/
theorem fc41_row_zero_closedGeometric_SFR :
    Nonempty (RawGraphPresentation zeroW) ∨
      (zeroW.model.boundary zeroW.Carrier = ∅ ∧
        ∃ G : GC.Geometry.GeometricStructure zeroW.model zeroW.Carrier,
          G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) :=
  exists_rawGraphPresentation_or_closedGeometric_of_fc41_row_SFR.{0} zeroW zeroStrong.1
    zeroStrong.2

end GC.GraphManifold.Assembly
