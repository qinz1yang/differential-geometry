# Smooth branch host acceptance, 2026-09-24

The isolated branch at e290b2f1d plus the repairs in this checkpoint passes strict
host acceptance. Main-checkout integration remains pending; isolated receipts
cannot serve as main-checkout compilation evidence.

- 741 modules: zero diagnostics, unchanged shared outputs.
- 632 changed or repaired modules, 27 audit shards, 11,086 declarations.
- All thirteen environment linters; transitive axioms contained in propext,
  Classical.choice and Quot.sound; no documentation-linter suppression.
- Entries: PlanarJordan.smooth_schoenflies, the boundary-germ extension theorem,
  and nonempty_diffeomorph_sphere_of_homeomorph_sphere.
- The frozen sphere statement is LF-identical to main (336 characters).
  Its proof explicitly consumes the retained CompactSpace S binder.

## Repairs

The checkpoint changes 274 Lean files plus the vendor modification record.
271 native modules received missing standard headers/module documentation or
line wrapping. Layout repairs preserve proofs; two qualified names were
shortened inside their namespace or a declaration-local open. Exact final
source hashes for every repaired path are in the receipt manifest.

Linter repairs remove unused finite-dimensional, Hausdorff, groupoid and
finite-face instances in PLHomeomorph, PLPiece, LinkEuclidean, Manifold,
Combinatorial, FrontierBoundary, Orientation, CylinderEndMap, PLBallSphere and
PLMap. The non-frozen sphere embedding consumer drops unused CompactSpace M.
The private PolygonalCrosscut cast lemma drops unused NeZero; its vendor
MODIFICATIONS.md records that edit while retaining provenance and attribution.
Proofs and dependants were recompiled. No linter disable, resource override,
new mathematical hypothesis or proof debt was added.

A broader incoming-name scan found pre-existing Real.smoothTransition.one_sub
in two modules registered by the aggregate. The cutoff integral module now
imports the canonical calculus theorem; its two integral lemmas pass a separate
strict compile and audit. This checkpoint introduces no new public name.

## Dependency freshness correction

The initial apparent 740/740 result was withdrawn: restart recovery had admitted
24 prior-day source-matching receipts with stale dependencies. Audit shard 20
exposed unknown constant ZMod.instField in three declaration types. The host
invalidated those modules and reverse dependants together with linter repairs:
274 modules, then 166 after propagated linter findings. Per-module verification
epochs are now enforced by the scheduler and private import-map validator.

All final 741 receipts pass checkout identity, source SHA-256, source stability,
zero diagnostics and dependency-epoch gates. The corrected 27 audits pass;
the separate TriangleRounding type/kernel diagnostic is empty. Compiler flags
and memory admission thresholds were unchanged; the owner authorized six slots.

## Pending integration

The branch adds 118 leaf paths relative to its merge base. Main must receive a
real merge, flat-root registration, source-bound dependency replay and the
PLSmoothingCompact promotion before its frozen-sorry ledger can decrease.
A repository-wide aggregate build is not certified by this isolated replay.
See smooth-isolated-host-receipts.json for receipts, audit counts, dependency
epochs and repair hashes.
