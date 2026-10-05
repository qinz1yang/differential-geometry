import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalLanding
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalSphereRegression

/-!
# FC39 GROUP G final landing: the S³ regression (lane FC39-G-FINAL, G2)

The pointwise landing `strongCertificateOfAdapted_GFIN` on the S³ prepared rows V2
(`spherePreparedV2_GGFF sphereJunctions`), the S³ safe neighbourhoods and the EXISTING S³ adapted
data V2 (`sphereJointAdaptedEdgeRimDataV2_GGFF`); vertex / port layers, seams / faces and arcs come
from the DELIVERED general theorems (`exists_vertexLayer_portLayer_G1`, `exists_seams_faces_GSF`,
`stub_exists_arcLayer_GARC`), not from the hand-made S³ layers.

* the result has two handles; its circle region, handles and rim charts are those of FC39-JOINT2's
  `sphereStrongCertificate` (**definitional**, `rfl`); its vertices / seams / faces / arcs are chosen
  by the general theorems, so equality of the whole certificate is not claimed — that equality
  holds for the data form with the hand-made layers (`sphereStrongCertificateOfRemaining_GFIN_eq`,
  rfl, G1);
* the existence form on S³.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- **The pointwise landing on S³** with the existing S³ adapted data V2. -/
def sphereStrongCertificateOfAdapted_GFIN :
    StrongCertificate sphereW (BoundaryTori.empty sphereW) :=
  strongCertificateOfAdapted_GFIN (spherePreparedV2_GGFF sphereJunctions)
    (sphereSafe sphereJunctions) sphereJointAdaptedEdgeRimDataV2_GGFF

/-- Non-vacuity: the S³ landing has two handles. -/
theorem sphereStrongCertificateOfAdapted_GFIN_handleCount :
    sphereStrongCertificateOfAdapted_GFIN.1.handleCount = 2 :=
  rfl

/-- **Regression (definitional)**: the circle region of the S³ landing is that of
`sphereStrongCertificate`. -/
theorem sphereStrongCertificateOfAdapted_GFIN_circ :
    sphereStrongCertificateOfAdapted_GFIN.1.circ = sphereStrongCertificate.1.circ :=
  rfl

/-- **Regression (definitional)**: the handles of the S³ landing are those of
`sphereStrongCertificate`. -/
theorem sphereStrongCertificateOfAdapted_GFIN_handle (h : Fin 2) :
    sphereStrongCertificateOfAdapted_GFIN.1.handle h = sphereStrongCertificate.1.handle h :=
  rfl

/-- **Regression (definitional)**: the rim charts of the S³ landing are those of
`sphereStrongCertificate`. -/
theorem sphereStrongCertificateOfAdapted_GFIN_rimChart (h : Fin 2) (b : Bool) :
    sphereStrongCertificateOfAdapted_GFIN.1.rimChart h b =
      sphereStrongCertificate.1.rimChart h b :=
  rfl

/-- The handles of the S³ landing are whole preimages of their labelled base components. -/
theorem sphereStrongCertificateOfAdapted_GFIN_handle_whole (h : Fin 2) :
    range (sphereStrongCertificateOfAdapted_GFIN.1.handle h).map =
      (spherePreparedV2_GGFF sphereJunctions).rows.edge.wholeComponent
        ((spherePreparedV2_GGFF sphereJunctions).rows.edgeModels.componentEquiv
          (.inl (sphereJointAdaptedEdgeRimDataV2_GGFF.labelled.edgeLink.handleEquiv h))) :=
  strongCertificateOfAdapted_GFIN_handle_whole (spherePreparedV2_GGFF sphereJunctions)
    (sphereSafe sphereJunctions) sphereJointAdaptedEdgeRimDataV2_GGFF h

/-- The existence form of the pointwise landing on S³ (through the delivered general theorems). -/
theorem sphere_strongCertificate_of_adapted_at_GFIN :
    Nonempty (StrongCertificate sphereW (BoundaryTori.empty sphereW)) :=
  strongCertificate_of_adapted_at_GFIN (spherePreparedV2_GGFF sphereJunctions)
    (sphereSafe sphereJunctions) sphereJointAdaptedEdgeRimDataV2_GGFF

end GC.GraphManifold.Assembly.FC39P0
