import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalClosed
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.ExtPortCertificateXPI

/-!
# FC39 GROUP G CLOSED: end-to-end regression on the external-port instance (D67-6 (b))

Lane FC39-G-RIMBOXc (FC39-G-FINAL G3 consumer). On the external-port rows `extportRowsW_XPI`
(`T² × I` with two ports, lane FC39-EXTPORT-INSTb) the GENERAL zero-argument chain gives the strong
certificate again — from the raw rows (`exists_strongCertificate_of_rows_GFIN`) and from the prepared
rows of the instance (`exists_strongCertificateV2_GFIN`) — and the RIMBOX producer
`exists_adaptedEdgeRimDataV2_GRIM` runs on the instance's general `GF` / `safe` (the hand-made adapted
data `extportAdaptedG_XPI` are no longer needed).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.ExtPortXPI

/-- **End-to-end regression (D67-6 (b)):** the external-port instance has a strong certificate
through the zero-argument theorem on its raw rows. -/
theorem extport_exists_strongCertificate_of_rows_GRIM :
    Nonempty (StrongCertificate carrierW_XPI portsE_XPI) :=
  exists_strongCertificate_of_rows_GFIN extportRowsW_XPI

/-- The same through the V2 prepared rows of the instance (general GFF output). -/
theorem extport_exists_strongCertificateV2_GRIM :
    Nonempty (StrongCertificate carrierW_XPI portsE_XPI) :=
  exists_strongCertificateV2_GFIN extportPrepared_XPI

/-- The RIMBOX producer on the instance's general `GF` and general `safe`. -/
theorem extport_exists_adaptedEdgeRimDataV2_GRIM :
    Nonempty (AdaptedEdgeRimDataV2 extportPrepared_XPI extportSafe_XPI) :=
  exists_adaptedEdgeRimDataV2_GRIM extportPrepared_XPI extportSafe_XPI

end GC.GraphManifold.Assembly.FC39P0.ExtPortXPI
