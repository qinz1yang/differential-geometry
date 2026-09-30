# Step 1: shared Lean foundation

September 28, 2026. Private destination:
`qinz1yang/differential-geometry-dev`, branch
`codex/geometrization-team-foundation`, based on baseline201 commit
`22b9d2a5a8323cff4bf5af72595a499b9e91f205`.

## Delivered

- A normal Lake library with 90 previously checked GC modules and 33 attributed
  third-party dependency modules. Selection comes from successful build receipts
  with matching source hashes. Historical experiments and RunAudit drivers are
  excluded; the frozen baseline is unchanged.
- `GC.Interface.RawSurgery`, using the actual PC manifold/metric/tower types.
  `ofInitial` invokes the existing general producer. Initial markings, finite
  event sets, actual event geometry and regular prefixes all use the same tower.
  Three independent consumer declarations exercise the interface.
- `GeometrizationChecks`, covering all accepted team modules and checking their
  transitive axioms. `tools/gc/check.py` checks imports, pins, provenance, source
  hygiene and task metadata, and runs the Lake target. Optional promotion
  comparison and forced fresh axiom audit are available.
- Positive and negative gate tests: a proved theorem is accepted; a new axiom
  and a proof placeholder are rejected. The fixtures are temporary and never
  become part of the accepted library.
- A detailed team plan, nine proposed task cards with disjoint write scopes,
  source records, contribution instructions and a PR template. Roles and claims
  require the team's agreement; no teammate was contacted or assigned work.
- Unchanged copies of the current master202 three-file blueprint, existing
  mathematical DAG and frontier, with snapshot hashes. No mathematical blueprint
  revision or new proof-closure classification is claimed.

## Verification

`lake build Geometrization GeometrizationChecks` passed. Lake reported 20,189
jobs including cached dependencies. All 128 team Lean modules, including root
and check modules, participate in the gate. The axiom audit passed for 3,503
declarations owned by the team modules, including visible private helpers and
vendored modules; transitive axioms were limited to `propext`,
`Classical.choice`, and `Quot.sound`.

The exact promotion comparison passed for all 123 promoted modules. Proof bodies
and declaration names are preserved. Imports changed, diagnostic prints were
removed, and original `autoImplicit=true` behavior was restored explicitly in
third-party files. Initial build failures exposed that configuration difference;
the corrected build passed. The new audit command's initial elaboration errors
were also corrected before acceptance. Existing linter warnings remain.

The isolated gate tests passed all three cases. Static checks cover 128 modules
and nine task cards, including import/task acyclicity and nonoverlapping write
areas. All 152 historical pilot source hashes remain unchanged. PC source files,
the Lean pin and the dependency manifest are unchanged.

The build ran on Bennett's Mac using a private copy-on-write copy of the already
audited PC/dependency build cache. Newly named team modules were compiled from
source. This is not a cold rebuild of the entire PC project or a validation on
another operating system. Lake import paths are repository-relative; no original
Mac path or custom `LEAN_PATH` is needed by the production library.

Machine-readable receipts and logs are in `evidence/`; source hashes bind the
result even when the precommit receipt reports a dirty worktree. The root
blueprint consistency check is separate from Lean and mathematical validation.

## Remaining work and rollout

The static GitHub workflow is supplied; it is explicitly not Lean verification.
The full gate is locally operational. Configuring a warm integration worker,
collaborator access and required branch checks remains repository-administrator
rollout work. No runner, branch protection, merge or pull request was created.
Use the team plan's contract review/claim step before dispatching the large
coding queue.

No new global cutoff profile, long-time control theorem, full marked
reconstruction or geometrization endpoint has been proved in this setup step.
The mathematical contribution is a checked shared interface over the existing
producer; most code here is the portable integration of the existing proofs.
