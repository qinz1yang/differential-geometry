# Subject placement for the Geometrization development

The user's instruction requires live modules to reside in their mathematical
homes under DifferentialGeometry, following NAMING.md and STRUCTURE.md, with
all pushes confined to Ziyang's private repository. This migration changes
placement and imports, not mathematical statements or proof arguments.

The authoritative DifferentialGeometry guides were absent from this checkout
and private main. Their clean tracked copies were read from the local wt30
checkout at94210f01eec433caeed0115d5c50e2881f7c3624 and copied to this branch.
The exact hashes are in MODULE_PLACEMENT.json. The similarly named vendored
PoincareLean guides have a different scope and were not substituted.

## Changes

- 153 live modules move out of Geometrization/GeometrizationChecks into their
  subject homes. Two genuine interfaces are split, yielding155 leaves.
- The compact metric/manifold finite-generation proofs live in
  Topology/FundamentalGroup/FiniteGeneration/CompactFundamentalGroup.lean.
  Their existing surgery-stage consequences live in
  Geometry/Flow/RicciFlow/Surgery/Topology/InitialFundamentalGroup.lean.
- The commutative free-product argument lives in
  Topology/Algebra/Group/FreeProduct/Commutative.lean. The smooth prime
  applications remain in Topology/ThreeManifold/Geometrization/StandardPrimes.lean.
- The remaining reusable topology, static geometry and analysis follow the
  subject directories enumerated in README.md. Flow-specific consumers live
 under Geometry/Flow/RicciFlow. Existing namespaces/public names remain stable;
  STRUCTURE section7 explicitly separates placement from namespace naming.
- The33 vendored modules move to attributed External homes with unchanged
 licenses/attribution and import-only source changes.
- Native comments/docstrings are removed under NAMING's source-text policy;
  mathematical explanations and source checks remain in documentation.
- The two former root aggregates and extra Lake libraries are removed.
  DifferentialGeometry.lean is the single flat aggregate. Every migrated leaf
  is registered, and no library leaf imports that root.
- The188 historical source snapshots remain byte-identical as .lean.txt evidence.
  They are no longer live modules outside DifferentialGeometry. Their original
  runnable form remains on the unchanged baseline201 branch and prior commits.

MODULE_PLACEMENT.json records every old/current file and module name, hashes,
the two split outputs and every archived-source translation. Historical
BASELINE_PROVENANCE_REVISION206.json is preserved. Current provenance points
to the text snapshots and the subject-home modules. Source receipts are not
rewritten to pretend their old builds used the new paths.

## Verification

`python3 tools/gc/check.py --verify-promotion` checks the current paths, flat
root membership, import reachability, source hygiene, provenance and proof-token
preservation against the206 commit before running `lake build DifferentialGeometry`.
The two split files are checked by exact namespace-body token comparison.
The only changed nonproof command is the axiom audit's exact155-module ownership
list. The gate checks that the list exhausts all migrated leaves.

The negative gate test compiles one proved fixture and rejects both a custom
axiom and a placeholder using the same audit command. Temporary fixtures are
excluded from the accepted library. Exact root-build and axiom results are in
the207 receipts after completion, separately from the static preservation checks.

This is not a new blanket review of all established public declaration names
or all accepted PC proofs. It preserves the existing mathematical API while
fixing module placement, source-text policy and build integration. No new
mathematical producer or full Geometrization proof is claimed.

The user requested a prompt stopping point after the blueprint was ready. The
broader root rebuild was deliberately interrupted; the bounded
`--owned-modules` gate verifies all155 relocated leaves and their actual
consumer/axiom checks. No successful whole-root rebuild is claimed for207.
