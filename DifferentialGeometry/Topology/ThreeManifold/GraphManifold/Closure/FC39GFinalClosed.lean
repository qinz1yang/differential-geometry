import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalLanding
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimAssembly

/-!
# FC39 GROUP G CLOSED: the strong certificate from the rows (lane FC39-G-FINAL G3, delivered by FC39-G-RIMBOXc)

The final landing `FC39GFinalLanding.lean` (lane FC39-G-FINAL) with its only remaining explicit
argument — the frozen V2 adapted statement (D58-1 / D58-4) — discharged by the RIMBOX theorem
`exists_adaptedEdgeRimDataV2_GRIM` (`FC39GRimAssembly.lean`). Template
`build-logs/scratch/FC39-G-FINAL/G3-FinalClosed.lean.txt`, verbatim:

* `exists_strongCertificate_GFIN` — the frozen final target `stub_exists_strongCertificate`
  (`T:369–371`) verbatim: every prepared row package (V1) has a strong certificate;
* `exists_strongCertificateV2_GFIN` — the frozen V2 final target `stubV2_exists_strongCertificate`;
* `exists_strongCertificate_of_rows_GFIN` — from the raw rows alone (global face functions produced by
  `exists_globalFaceFunctions_GGFF`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- **GROUP G CLOSED: the frozen final target `stub_exists_strongCertificate` (`T:369–371`) verbatim.** -/
theorem exists_strongCertificate_GFIN (Pr : FC39Prepared W E) : Nonempty (StrongCertificate W E) :=
  strongCertificate_of_adapted_V1_GFIN Pr exists_adaptedEdgeRimDataV2_GRIM

/-- The frozen V2 final target `stubV2_exists_strongCertificate (Pr)` (D58-1). -/
theorem exists_strongCertificateV2_GFIN (Pr : FC39PreparedV2 W E) : Nonempty (StrongCertificate W E) :=
  strongCertificate_of_prepared_adapted_GFIN Pr exists_adaptedEdgeRimDataV2_GRIM

/-- From the raw rows alone (global face functions produced by `exists_globalFaceFunctions_GGFF`). -/
theorem exists_strongCertificate_of_rows_GFIN (Rw : FC39RowsV2 W E) : Nonempty (StrongCertificate W E) :=
  strongCertificate_of_adapted_GFIN Rw exists_adaptedEdgeRimDataV2_GRIM

end GC.GraphManifold.Assembly.FC39P0
