# Step 1 source and scope record

Date: September 28, 2026. This is a Lean integration/refactoring task, not a new
mathematical proof route. No new claim from a paper or book is imported. Existing
source checks and mathematical qualifications in the frozen blueprint remain
in force; no retrospective rereading of the whole archive is claimed.

Accepted foundation: public PC v0.1.3,
`7a48598d35109aa99d1cc678e2724c213cdf4ff3`; Lean v4.33.1,
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The development repository has
the identical PC source tree. No PC theorem is strengthened or rewritten here.

Bodies inspected for the new interface:

- PC `Geometry/Flow/RicciFlow/Surgery/Topology/RetainedCoreTower.lean`, lines
  25–176: actual event, history, retained-core observation tower and projection
  to the observation tower. Initial metric compatibility is retained.
- PC `Geometry/Flow/RicciFlow/Surgery/Topology/ObservationTower.lean`, lines
  35–55: restriction, `observe`, `observeInitial`, and horizon equality.
- Frozen revision201 `CoherentSurgeryTower.lean`, whole file: integer-history
  recursion, actual general producer, event controls, event geometry, local
  finiteness. `GeneralTowerConsumers.lean`, whole file: marked regular prefix
  and the precisely qualified empty/nonempty alternative.
- Frozen revision175 `TowerFinitePrefixes.lean`, whole file, and
  `TowerConsumers.lean`: regular-time consumers on a supplied actual tower.
- Frozen revision201 `SurgeryEventControl.lean`: local controls are incoming
  singularity, boundary frame reversal and standard discarded components.

The new bundle contains that actual tower and those actual proved controls.
Its existence is discharged by revision201's producer. All projection theorems
use the same stored tower. It adds no global analytic predicate or final
geometric conclusion. Initial identification is retained explicitly rather than
inferred merely from the history's type parameter.

`BASELINE_PROVENANCE.json` records every promoted source and original build
receipt hash. Selection requires a successful recorded build and matching
source hash; RunAudit drivers, probes, rejected-profile tests and failed
experiments are excluded. The migration changes imports, removes standalone
diagnostic `#print axioms`, and adds provenance notices. Third-party files
explicitly restore the `autoImplicit=true` setting of their standalone builds;
the first Lake build exposed this previously implicit requirement. The original
proof bodies and declaration names are preserved. The migration comparison is
checked mechanically, and all promoted files are freshly compiled under their
new module names. That is separate from the original receipts.

The 19 Kurosh and 14 Grushko compatibility modules retain their Apache-2.0
licenses and notices under `Geometrization/Vendor/`. Their original repository
pins and earlier compatibility modifications are recorded in those notices.
The original source receipts remain in the frozen baseline. Moving imports does
not change the theorem statements; the full team axiom gate checks the new
compiled declarations including their transitive upstream axiom dependencies.

Lean's axiom collector was checked in the installed v4.33.1 source,
`src/lean/Lean/Util/CollectAxioms.lean`, especially `collectAxioms` and the
imported axiom extension. The team gate uses `env.checked` for declaration
existence and that collector for transitive axiom dependencies. This checks
proof trust, not mathematical adequacy of a theorem's assumptions.

Existing DAG and task locators are reused from planning revision202. Scheduling
cards do not certify new mathematical dependency edges or close open leaves.
No new source/errata comparison for the future packets is claimed.
