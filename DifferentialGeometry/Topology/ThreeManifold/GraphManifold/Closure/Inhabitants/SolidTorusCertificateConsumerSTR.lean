import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusCertificateSTR

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G7c consumer

The geometry under the certificate is not vacuous: next to `strongCertificate_STR` the circle region
contains the actual point `p*` over `q* = (7/8) i`, the face facts have two actual endpoints on the
same ball face whose whole rims are disjoint, non-empty circle fibres over the distinct corner
points `q±`, and the descended face equation has `b' ≠ 0` at both endpoints.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

/-- **The boundary-route acceptance instance, non-vacuously**: the strong certificate, a non-empty
circle region, and two actual corner incidences on the same ball face. -/
theorem certificate_nonvacuous_STR :
    Nonempty (StrongCertificate Wc X135Radial.boundary) ∧
      rows_STR.circle.region.Nonempty ∧
      ∃ e₀ e₁ : rows_STR.edge.EdgeEnd, e₀ ≠ e₁ ∧
        faces_STR.horizontal e₀ = faces_STR.horizontal e₁ ∧
        qOfBase_STR (rimBase_STR e₀.1).1 = qPlus_STR ∧
        qOfBase_STR (rimBase_STR e₁.1).1 = qMinus_STR ∧
        Disjoint (rows_STR.edge.rim e₀.1) (rows_STR.edge.rim e₁.1) := by
  refine ⟨strongCertificate_STR, ?_, ?_⟩
  · obtain ⟨p, hp, -⟩ := region_nonempty_STR
    exact ⟨p, hp⟩
  · obtain ⟨e₀, e₁, h1, h2, h3, h4, -, h6, -⟩ := corner_incidences_STR
    exact ⟨e₀, e₁, h1, h2, h3, h4, h6⟩

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
