# Canonical topology migration record

The former top-level `canonical-topology/` project (`PoincareLean`, 89 Lean
modules) has been migrated into this repository. Its mathematical content now
lives under `DifferentialGeometry/Topology/Homology/` and
`DifferentialGeometry/Analysis/`, with the following local changes:

* namespaces and imports were rewritten from `Poincare.*` to
  `DifferentialGeometry.*` (and imports were redirected to the current module
  paths of this repository);
* comments and docstrings were removed to comply with this repository's
  zero-comment source rule for non-vendored Lean sources;
* `SmallChains.lean` and `Relative.lean` were relocated to
  `Topology/Homology/SmallChains/Basic.lean` and
  `Topology/Homology/Relative/Basic.lean` respectively, whose statements are
  supersets of the migrated ones;
* `Analysis/LocalDerivativeHomotopy.lean` was placed at
  `Analysis/Calculus/Derivative/PuncturedBallDerivativeHomotopy.lean`;
* `Topology/Homology/LocalDerivativeComparison.lean` and
  `Topology/Homology/LocalLinearMaps.lean` were added verbatim up to the
  namespace, import and comment changes above;
* `LocalCharts.lean` gained the missing naturality theorem
  `integralLocalHomologyOpenPartialHomeomorphIso_natural`.

The upstream provenance material of the recovered project (`APACHE-2.0.txt`,
`README.md`, `PROJECT_CONTEXT.md`, `RECOVERED_AGENTS.md`,
`RECOVERED_PROJECT_CONTEXT.md`, `SNAPSHOT.json`) is preserved in this
directory. The recovered sources derive from commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad` of the recovered Chapter 35
development, and `Analysis/LocalDerivativeHomotopy.lean` was adapted from
`plby/HopfProblem` (Apache-2.0, commit `9ac8a45`, lines 62156-62228).
