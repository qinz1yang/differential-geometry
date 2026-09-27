# Selected Tau Ceti source

Source repository: https://github.com/TauCetiProject/TauCeti

Pinned commit: `3358033ba2fd35f321356dceaf2372a0fd6c0bfd`. Only selected proofs from five source files are archived, together with the original LICENSE and README. The full Tau Ceti library and dependency configuration are not installed or vendored.

The active vendor contains equal-dimensional Sard, derivative genericity for Morse perturbations, and immersion/slice chart proofs. Existing DifferentialGeometry public names are preserved. Native full Sard, Hessian bridges, smooth-embedding corollaries, and extension/gluing mathematics remain in their original topic directories.

Original code and documentation are preserved in `upstream/selected-3358033.tar.gz`. The source is Apache-2.0, by Joseph Tooby-Smith, Codex and The Tau Ceti contributors as recorded in the individual original source headers. See LICENSE, SOURCE_MAP.json, DECLARATION_MAP.json and MODIFICATIONS.md.

`python3 DifferentialGeometry/External/TauCeti/migrate.py --check` verifies the selected-source migration. `--apply` replays it after validating source and consumer hashes.
