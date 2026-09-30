# Geometrization working handoff

The current blueprint is **revision207**. Blueprint writing is wrapped up.
The user subsequently authorized a [Lean skeleton with explicit admissions](skeleton/README.md)
and checked assembly proofs. Its public capstone depends on `sorryAx`; it is not
a completed proof of geometrization. All live
Lean modules are in their mathematical homes under `DifferentialGeometry/`.
Follow the repository's [NAMING.md](../../NAMING.md) and
[STRUCTURE.md](../../STRUCTURE.md). The only root library aggregate is
`DifferentialGeometry.lean`; no separate Geometrization library remains.

The destination for all pushes is the verified private repository
`qinz1yang/differential-geometry-dev`, branch
`codex/geometrization-blueprint-skeleton-207`. The proof-complete baseline remains
on `codex/geometrization-team-foundation`. Ziyang controls integration. The
historical `codex/geometrization-baseline-201` branch is unchanged.

## Current mathematical status

The endpoint statement has concrete prime factors, torus cuts, complete
whole-interior fixed-model geometry and oriented reconstruction. It is
`GC.Endpoint.GeometrizationConjecture`, in
[DifferentialGeometry/Topology/ThreeManifold/Geometrization/Statement.lean](../../DifferentialGeometry/Topology/ThreeManifold/Geometrization/Statement.lean).
**The universal theorem is not proved without admissions.** The new
`GC.Endpoint.geometrization` in `Geometrization/Theorem.lean` assembles this same
target from the explicitly admitted producers; see the skeleton audit for its
exact transitive assumptions.

Revision206 proves full certificates for the actual PC standard factors.
The actual empty-observation history consumer now needs only that observed
emptiness. The late consumer requires `LateComponentSupply F.observation` on
the same raw tower. One controlled global flow/profile and its late geometric
suppliers remain open. No arbitrary raw tower is asserted to have that supply.
Stronger protected-port, prescribed-cycle and decorated-history exports remain
separate from the bounded endpoint descent.

Read [the current blueprint handoff](blueprint/BLUEPRINT_HANDOFF_REVISION207.md),
[the endpoint audit](ENDPOINT_AUDIT.md), and [the team plan](TEAM_PLAN.md).
The existing DAG and current-view overlay remain the mathematical map; task
cards only schedule work and do not establish proof dependencies or acceptance.

## Mathematical module homes

- Free products and finite generation: `Topology/Algebra/Group/FreeProduct/`
  and `Topology/FundamentalGroup/FiniteGeneration/`.
- Collars, van Kampen and three-manifold cuts: `Topology/VanKampen/FreeFactors/`
  and `Topology/ThreeManifold/`.
- Metric scaling, approximation and model geometry: `Geometry/Metric/` and
  `Geometry/Thurston/`.
- Common positive profiles: `Analysis/Order/CommonProfile.lean`.
- Actual flow-specific applications: `Geometry/Flow/RicciFlow/Perelman/`
  and `Geometry/Flow/RicciFlow/Surgery/`.
- Attributed third-party algebra: `External/GraphCoveringTheory/` and
  `External/GrushkoNeumannTheorem/`.

[MODULE_PLACEMENT.json](MODULE_PLACEMENT.json) translates every old live module
path to its current home and records two genuine algebra/topology separation
boundaries. Public declaration names are preserved, as STRUCTURE section7
requires no namespace churn merely for a file move. Native Lean comments have
moved out of the source; mathematical/source explanations remain in the docs.
Vendor attribution and licenses follow their sources.

The188 historical `.lean` snapshots under `Examples/GeometrizationBaseline/`
are preserved byte for byte as `.lean.txt`. They are read-only evidence, not
importable modules. Original build records retain their historical paths;
the placement manifest gives the translation. The baseline201 branch preserves
the original executable snapshot. Do not import or recreate that archive.

## Verification

The toolchain remains Lean4.33.1 with accepted PC v0.1.3 and the recorded
Mathlib commit. Clone only the private repository:

```sh
git clone --branch codex/geometrization-team-foundation https://github.com/qinz1yang/differential-geometry-dev.git
cd differential-geometry-dev
lake exe cache get
python3 tools/gc/check.py --verify-promotion
```

The normal root build is `lake build DifferentialGeometry`. For a bounded
check of all155 relocated leaves, use
`python3 tools/gc/check.py --verify-promotion --owned-modules`; the audit
consumer imports every owned leaf. This does not certify a fresh whole-root
rebuild. The207 whole-root run was stopped at the user's requested stopping
point; the bounded result is recorded separately. Every public leaf,
including the actual consumer checks, belongs to the flat root aggregate.
Library leaves never import that aggregate. The wrapper checks placement,
import reachability, pins, source hygiene, task metadata, provenance and the
compiled axiom audit. `--verify-promotion` additionally checks the exact
migration's proof-token preservation against its recorded Git commit.
The current migration receipt is not a ban on future reviewed proof edits;
future edits need new honest evidence, not rewriting historical receipts.

A narrow example is:

```sh
lake build DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawSurgery
```

`--static` performs no Lean execution. `--fresh-audit` reruns the compiled
axiom command. `python3 tools/gc/test_axiom_gate.py` checks acceptance of a
proved fixture and rejection of an axiom and placeholder in temporary files.
The audit covers every migrated owned module, including private helpers and
vendor declarations; only `propext`, `Classical.choice`, and `Quot.sound` are
allowed. An axiom audit does not establish adequacy of a theorem's hypotheses.

The lightweight CI workflow remains static only. A full Lean worker and merge
requirements remain integration decisions. Local builds reuse accepted caches;
no cold-machine or independent teammate acceptance is claimed. The current
build outcome is in the207 receipt;206's155-module/4311-declaration receipt
is preserved with its original source hashes and precommit HEAD.

## Historical records

[STEP1_REPORT.md](STEP1_REPORT.md) and [SOURCE_CHECKS.md](SOURCE_CHECKS.md)
describe the original promotion. INTERFACE_ITERATION203 through206 describe
subsequent mathematical increments at their original module locations.
Their status and command examples are historical; use this README, the207
handoff and the placement manifest for current navigation.
