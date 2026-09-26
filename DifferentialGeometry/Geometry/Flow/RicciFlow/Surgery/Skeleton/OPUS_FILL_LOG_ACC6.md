# ACC6 acceptance log

- 2026-09-26T13:10Z start: base a161fc07e. Scope: 14 new modules (SFR 3, SG3 1, L4E 2, L10 1,
  C3B2 1, B7 1, B3d 1, B6b' 1, L10b 2, H3b 1), all present. Closure of the build targets checked:
  no untracked or modified module outside the accepted set (in-flux H6 `Index`, H7A `Jacobian`,
  SB14 `UniformDebitSurgeryStepOfFactory`, and the untracked `HornSeparationFrontierScalar` are not
  in it). `Perelman/CanonicalNeighborhood/CapCoreCylinderAbsorption` (committed 92795429c) is in the
  closure but absent from the root aggregate; it is imported by five registered modules, so it is
  built; left as is.
- Root aggregate: 13 modules appended, `HistoryLGeometry.ExponentialSmooth` after `MinDomain`.
- Placement: `CheegerGromovCompactness.curvDerivNormSq_restrictOpen` (L10b, `RetainedCrossingJets`)
  belongs in `Geometry/Curvature/CurvatureOperator/Derivatives/Restriction.lean` (next to
  `curvDerivNorm_restrictOpen`), but that file has 1736 transitive dependents: NOT moved now
  (seven worker compiles running); recorded in FILL_QUEUE `merges` for a quiet window.
- 2026-09-26T13:13Z build1 (one lake call, 10 leaf targets incl. `PoincareEndgame`).
  13:13:30Z-13:22:20Z exit 0, 19680 jobs; only output: the 8 `declaration uses sorry` warnings of
  `PoincareEndgame`.
- 2026-09-26T13:32Z audit (`AuditAcc6.lean`, 13:22:38Z-13:32:47Z): 156 declarations of the 14
  modules; every declaration within [propext, Classical.choice, Quot.sound];
  `capWindowContinuation_of_slab_interior`, `capWindowContinuation_of_slab_start_bounds`
  [propext, Classical.choice, Quot.sound]; `smoothPoincareConjecture_holds` adds `sorryAx` (the 8
  leaves). Linters: 6 `defsWithUnderscore` failures, all SG3's data-valued `mono_eps` defs
  (`SpatialOrderedNeckChain`, `SpatialLocalNeck`, `SpatialLocalCap`, `SpatialRoundComponent`,
  `SpatialCanonicalAlternative`, `SpatialCanonicalWitness`). Repaired: renamed to `monoEps` (simp
  lemma `SpatialCanonicalAlternative.monoEps_requiresVolume`); the Prop-valued theorems keep
  `_mono_eps` (`spatiallyCanonicalBefore_mono_eps`, the one SB14 uses, is unchanged). The committed
  time-0 analogues in `CanonicalToleranceMonotone` (`CanonicalWitness.mono_eps` etc.) carry the same
  debt; not touched. build2 (the module) 13:33:35Z-13:34:11Z exit 0; re-audit of the module: 11
  declarations, 0 failures, 13 linters clean.
- Ledgers: FREE_INPUTS (ACC6 section, S row), FILL_QUEUE (22 bricks, C3b, Crossing, S bricks,
  merges), HANDOFF_S (F* paragraph with `FineCutNecks` and the binder order, checked against the
  source). Review F digest committed. `git diff --check` clean. Committing.
