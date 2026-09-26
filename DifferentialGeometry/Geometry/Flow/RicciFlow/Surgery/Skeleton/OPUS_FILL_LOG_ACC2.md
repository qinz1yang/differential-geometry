# ACC2 acceptance log

- 2026-09-26T08:29:10Z start: base d99671988; deliveries E3, D2, 26, X2, 27a, 18c.
- 2026-09-26T08:31:41Z moves done: E3 private duplicate removed (CanonicalWitnessComparisonTransport, unused M variable dropped); D2 order-j standard-cap bound -> StandardCurvatureComparison, two pullback-scaling lemmas -> LocalPullbackScaling (+LocalCross import); X2 ball lemma -> RestrictionDistance (+Distance.Ball import, uses existing private path lemma); 27a five general declarations appended to SpatialCanonicalWitness; 7 modules registered in root.
- 2026-09-26T08:33:22Z build1 running: [19063/19213]
- 2026-09-26T08:44:02Z build1 running: [19148/19213]; SpatialCanonicalWitness failed (SecLower.mono not imported) -> added import CanonicalStrictBounds (no cycle; +1 module in closure)
- 2026-09-26T08:56:34Z build2 (184s): SCW fixed; transient 'failed to read olean' in lane-28-dependent modules (host memory); real failure: CapWindowDerivativeBounds heartbeat timeout at 266/273. Coordinator: drop PoincareEndgame target, add G7 closure.
- 2026-09-26T09:02:29Z build3 (278s, 19207 jobs): all targets built except CapWindowDerivativeBounds (heartbeat timeout 266/273, reproducible)
- 2026-09-26T09:09:00Z CWDB repaired without statement change: extracted abs_scalar_derivatives_le_of_scaled_curvature_jets (generic, PDE.RicciFlow), linarith -> linarith only in 6 places, removed n/Kd/Kg set-abbreviations; standalone probe passes at maxHeartbeats 100000 (was >140000 needed)
- 2026-09-26T09:10:02Z build4: exit 0, 45s, [19207/19207], 0 errors/warnings/infos (builds: 1 1221s, 2 184s, 3 278s, 4 45s)
- 2026-09-26T09:20:34Z audit1 (9m54s): axioms all foundational (35 public theorems); 4 defsWithUnderscore in pre-existing NeckTransportDecoupled defs (file-local uses only) -> renamed StrongNeck/SpatialNeck.transportOfComparisons', transportOfComparisonsOfTolerances
- 2026-09-26T09:36:31Z build5 (944s): 2 host-OOM failures (DiagonalCapMetric olean read, WindowedCapLimit INTERNAL PANIC out of memory), not source errors; build6 relaunched with LEAN_NUM_THREADS=6
- 2026-09-26T09:51:28Z build6: exit 0, 881s, 0 errors/warnings/infos
- 2026-09-26T09:56:42Z re-audit NeckTransportDecoupled: 23 decls, 0 failures. git diff --check clean. Committing.
