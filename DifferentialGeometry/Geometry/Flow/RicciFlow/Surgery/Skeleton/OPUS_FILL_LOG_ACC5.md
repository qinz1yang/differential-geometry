# ACC5 acceptance log

- 2026-09-26T12:20Z start: base 950618ee3. Scope: I28c interface edit (SpatialCanonicalContinuation,
  CanonicalNeighborhoodsThroughSurgeryStrong) + 13 new modules (SPT 2, SB4 2, H3a/H4/H5 3, B8 1,
  B3c 3, C3b assembly 2). Closure of the build targets checked: no untracked or modified module
  outside the accepted set (in-flux SFR/H3b/H6/L10/L4E/B7 files are not in it). Registered
  dependents of the two edited modules: none besides the unregistered `Skeleton.PoincareEndgame`.
- Placement: B8's generic `exists_uniform_canonicalWitness_with_cap_neck_charts_of_windowedModelWitness`
  moved verbatim (pure move) to the new `Perelman/CanonicalNeighborhood/WindowedModelCanonicalWitness.lean`
  (imports `WindowedBufferedCanonical`; B8's module now imports it instead). A new file rather than
  `WindowedBufferedCanonical.lean` itself: editing that file rebuilds 184 dependents under six
  concurrent worker compiles. `partialDiffeomorphOfInjective` NOT moved: its home
  `Topology/Manifold/LocalDiffeomorphRange.lean` has 1040 transitive dependents; the pure move is
  deferred to a quiet window (no worker compiles), recorded in FILL_QUEUE.
- Root aggregate: 14 modules appended (HistoryLGeometry after `Seam`).
- 2026-09-26T12:28Z build1 (one lake call, 7 leaf targets: SpatialCanonicalWitnessComparisonTransport,
  PoincareEndgame, AncientLimitCanonicalWitness, BoundedCurvatureAtDistance,
  CapWindowContinuationAssembly, DiscardedSpatialClassification, HistoryLGeometry.Truncation)
  12:23:06Z-12:27:54Z exit 1: my new WindowedModelCanonicalWitness had too few `open`s (fixed:
  the same opens as WindowedBufferedCanonical); BoundedCurvatureAtDistance hit a host olean-read
  failure (mathlib QuasiCompact.olean), not a source error. build2 = same call 12:28:00Z-12:29:15Z
  exit 0, 19480 jobs; only output: the 8 `declaration uses sorry` warnings of PoincareEndgame.
- 2026-09-26T12:39Z audit (`AuditAcc5.lean`, 12:29:20Z-12:38:47Z) exit 0: 226 declarations of 16
  modules (14 new + the 2 I28c-edited), 0 failures; 119 public theorems, all within [propext,
  Classical.choice, Quot.sound]; 13 linters clean. `canonicalNeighborhoodsThroughSurgeryStrong_of_leaves`
  [propext, Classical.choice, Quot.sound]; `smoothPoincareConjecture_holds` adds `sorryAx`, and a
  closure trace (215191 constants) finds exactly 8 constants using `sorryAx` directly: the 8 leaves.
  `git diff --check` clean. Ledgers: FREE_INPUTS (C4 row, ACC5 section), FILL_QUEUE (22 bricks,
  C3b, Crossing, S bricks, new C4 row, merges), HANDOFF_C (C4 interface paragraph); LEAD_NOTES
  line 59 trailing space removed. The consult file `F-crossing-core-review-request.md` was already
  committed by the lead (d42db0554). Committing.
