import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12EnhancedC11E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileFullC11F
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6A12V11Fin0FS

set_option autoImplicit false

/-!
# A12' admission: `exists_surgery_with_decaying_accuracy_enhanced`

The `sorry` introduced by the A12' endpoint re-point (REPOINT-A12enh-20261006.md, step 2a;
user GO via the lead, 2026-10-07) is now replaced by a proof term: the 0-binder candidate D
`ObservedHistory.a12EnhancedFull_v11fin0_FS` (`P6A12V11Fin0FS`; INT-CH8 admission swap,
lead release 2026-10-08, ahead of R-C11-28; reversible).
The statement is `Ch11.A12EnhancedConclusion_C11E P g`: A12
(`exists_surgery_with_decaying_accuracy`) with its last conjunct `hasAnalyticAdmissibility F delta`
replaced by `Ch11.hasEnhancedAdmissibility_C11E F delta`. It takes the ledger place of A12;
A12' implies A12 without `sorry` (`Ch11.exists_surgery_with_decaying_accuracy_of_enhanced_C11E`).
M2-pre (O-CH11-MERGE, 2026-10-07, lead ruling U1): the statement is now the v2 form
`Ch11.A12EnhancedFullConclusion_C11F P g` (RFC-a field in the universal form of the ch12 terminal
binder `hRFCa`, "RFC-a universal per ch12 S148"); v2 implies the previous form without `sorry`
(`Ch11.a12EnhancedConclusion_of_full_C11F`).
The endpoint (`Geometrization.lean`, `GeometrizationEND0.lean`) feeds it to
`Ch11.geometrizes_of_metric_C11R` / `Ch11.exists_surgery_with_late_sequence_tests_C11R`.
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime

universe u

/-- The A12' admission (statement = `Ch11.A12EnhancedFullConclusion_C11F P g`). -/
theorem exists_surgery_with_decaying_accuracy_enhanced (P : OrientedThreeStage.{u}) (g : P.Metric) :
    Ch11.A12EnhancedFullConclusion_C11F P g :=
  ObservedHistory.a12EnhancedFull_v11fin0_FS.{u} P g

end GC.LongTime

end
