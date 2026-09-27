# B3e (lane B3F) — bounded curvature at distance on an arbitrary slice (2026-09-26)

- 06:57 Read AGENTS.md, DESIGN_MAXWINDOW (M1, §3.1), logs B3C/B3D/B3E/B5, the B3c/B3d/L1 files,
  X2 (`BackwardTraceDistortion{,Terminal}.lean`), B5, TracedTerminalCompactness supplier.
- Findings (route):
  (F1) The window of B3d enters only as "no events in the backward window" in two places:
  the first-level buffer (L1, `first = last`) and the second-level buffer at the cone-end points
  (`final_slab_scalar_buffer_of_spatialCanonicalWitness`). Both consumers
  (`exists_terminal_pointed_convergence_of_buffered_backward_traces`,
  `exists_nonnegative_local_flow_with_comparison_of_final_slab_window`) already accept traces
  through events (`∃ first, traces ∧ time first ≤ s − θ/Q`). So B3e = B3d with both buffers
  produced from traces.
  (F2) "Cone argument verbatim on the survivor flow" is NOT enough as briefed: the second-level
  points y_m sit near the escape radius, and a trace depth coming from the base ball has size
  1/(Ctime·sup_{B(y,d(y,y_m))} R), which is not comparable to 1/R(y_m) in general. Per-point X2
  capture at y_m only yields CapWindowPoint(y_m), not at the base.
  (F3) Fix used here: X2's capture with the ball replaced by a CHAIN of balls starting at the base
  (union of B(p_k, δ_k), consecutive centres inside the previous ball; the distance distortion is
  summed along the chain). The chain from the base runs (i) along a sublevel-minimising curve from
  y to the rebased point x (R ≤ max(q,R(y)) along it), (ii) along the images of the first-limit
  ray g up to the cone-end point, (iii) the witness ball at y_m. Along the ray the scalar is
  bounded by K'·R(xW_m) (necks of the neck sequence cover consecutive centres; R·d² ≤ C at the
  neck centres), so the chain sup is ≤ K'·R(y_m) and ¬CapWindowPoint(y) at the growing window
  size D_i gives the second-level traces at depth θ₂/R(y_m) with θ₂ uniform.
- Plan (files under Surgery/Topology/): ChainCapture (C1), ConeEndRayBound (C2), TracedLimit /
  TracedCone / TracedPositive (C3–C5, copies of L1/B3d with trace inputs), headline in B3d form
  (terminal slab), event-slab version via a prefix history, sequence corollary for §3.2b.
- 07:38 progress (all compile clean with `LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3
  -Dweak.linter.mathlibStandardSet=true`, default async elaboration, no output):
  `BackwardTraceChainCapture.lean` (chain-of-balls X2 capture: `riemannianEDistOf_lt_sqrt_mul_sum_of_ball_chain`,
  `capWindowPoint_of_chain_point_without_trace{,_of_activeStage_eq_last}`),
  `BoundedCurvatureAtDistanceTracedLimit.lean` (L1 with a trace-buffer input),
  `BoundedCurvatureAtDistanceTracedCone.lean` (second-level limit and cone exclusion with traces at
  the cone-end points; buffer from traces), `ConeEndRayScalarBound.lean` (punctured cone end +
  R ≤ K·R(xW_n) along the ray before xW_n; R·(b−s)² ≤ 2C on the ray tail).
- Lean pitfall (for the lead): in async elaboration (the CLI and lake default), a theorem header that
  mentions `F.partialDiffeomorph n x` while the body `let`s `F.partialDiffeomorph (k m) x` blew the
  heartbeat budget in `cleanup.letToHave` (40k heartbeats sync, >200k async). Writing the header
  with `F.map n x` (a def, different head) fixes it.
- 08:05 Review G received (chain capture with sup R ≤ K·R(y_m) along the whole path; survivor data
  across all events; completeness from ball exhaustion). This is the route already in progress:
  (1) chain capture + ray bound give exactly the per-path control at the scale of y_m (file
  `BoundedCurvatureAtDistanceChainBuffers.lean`, `exists_trace_first_on_witness_ball_of_ray_chain`,
  M ≤ K₃·R(y_m)); (2) the two limits use the committed trace-general suppliers
  (`exists_terminal_pointed_convergence_of_buffered_backward_traces`,
  `exists_nonnegative_local_flow_with_comparison_of_final_slab_window` → historical solution with
  traces through events, pinching of the survivor pullback, κ tests through
  `normalized_terminal_ball_volume_lower_bound_of_scaled_tests`), fed with `∃ first, traces` buffers.
  Compile method changed: my new modules are compiled as scratch modules `B3FScratch.*` (sources
  copied to the scratchpad, imports rewritten, `lean -R <scratch>/src -o <scratch>/olean/...`,
  LEAN_PATH = scratch olean dir + lake path); nothing is written under the project's `.lake`.
- 08:45 DONE (compiled): `BoundedCurvatureAtDistanceChainBuffers.lean` (first/second-level buffers from
  chain traces), `BoundedCurvatureAtDistanceTracedSecondLevel.lean` (second-level traces along the
  first-limit ray chain, θ₂ = secondLevelTraceDepth K C2 Kc θ Ctime uniform),
  `BoundedCurvatureAtDistanceTracedPositive.lean`: `RetainedCoreHistory.exists_normalized_scalar_bound_of_chain_traces`
  (B3d's positive form with the window replaced by a per-history chain-trace input `htrace`, plus
  `Q_i·time_i → ∞`, `D_i → ∞`), `BoundedCurvatureAtDistanceSlice.lean`:
  `chain_traces_of_not_capWindowPoint_of_incomingSlab` (¬CapWindowPoint(y, Dcap, θ) ⇒ `htrace` for
  chains prepended by a chain from y). Next: rebase chain (sublevel minimiser), terminal headline.
- 09:20 compiled: `OrientedThreeStage.ClosedSlab.exists_rebase_chain` (sublevel-minimising curve from y
  to the level max(q,R(y)), chained by gradient balls, total length ≤ 2d(y,z)+2r₀), and the
  sequence contradiction `false_of_terminal_counterexamples` in `BoundedCurvatureAtDistanceSliceTerminal.lean`
  (rebase chain + ¬CapWindowPoint(y, D_n, θ) with D_n → ∞ give `htrace`; positive form; bound at
  normalized distance 2A√K+1). Next: the ∃-headline, event-slab version, sequence corollary.
- 09:50 TERMINAL SLAB DONE: `RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal`
  and the sequence corollary `…eventually_scalar_bound_at_distance_of_not_capWindowPoint_terminal`,
  plus `RetainedCoreHistory.CapWindowPoint.mono` (M7b). Axioms (scratch `#print axioms` on the
  scratch module): propext, Classical.choice, Quot.sound. Next: event slabs via a prefix history
  `RetainedCoreHistory.prefixAt` and transports (records, CapWindowPoint, class, slabs,
  noncollapsing).
- 10:40 EVENT SLAB DONE (compiled, axioms propext/Classical.choice/Quot.sound):
  `RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_event` and the sequence
  corollary `…eventually_scalar_bound_at_distance_of_not_capWindowPoint_event`
  (`BoundedCurvatureAtDistanceSliceEvent.lean`), with the hypothesis `H.NoncollapsedBefore κ ρ t` on the
  whole history. Reduction: the prefix history `H.prefixAt j.castSucc` (`RetainedCoreHistoryPrefix.lean`)
  with `G := (H.toHistory.event j).incoming`, then the terminal headline. Transports in
  `RetainedCoreHistoryPrefixTransport.lean`: records (`prefixRecords`), class family, `EventSlabsDerivative`,
  `EventSlabsPinched`, `CapWindowPoint` (prefix ⇒ H), and noncollapsing
  (`noncollapsedBefore_eventPrefix`: the extended prefix agrees with H on stages, metrics and active
  stages for times ≤ T < T_{j+1}; traces transported).
- Lead flag F-g (base-slice data). The theorem stays a slice statement. Data that the proof uses ON the
  base slice t: (i) the witnesses `hW` at t; (ii) `¬CapWindowPoint(y, t, Dcap, θ)`; (iii) noncollapsing
  up to and INCLUDING t (`TerminalNoncollapsedBefore … t`, used with T = t for the κ tests of the first
  limit; in the event form `H.NoncollapsedBefore κ ρ t`); (iv) pinching on `Ico (slab start) s ∋ t`
  (terminal) or `EventSlabsPinched` (event); (v) the scalar values at (y, t) in `q ≤ Cq R`, `Λ ≤ R`,
  `Λ ≤ R t`, `Λ ≤ ρ √R`. `DerivativeBoundBefore` and `GradientBoundBefore` are used only on the open
  interval `Ioo a t`; the gradient balls of the rebase chain at t come from the open interval by
  continuity (`exists_rebase_chain`). So (iii)–(iv) are the only base-slice inputs besides witnesses and
  the traced (non-cap-window) condition; at slices σₙ < t₀ₙ both are available from the "before" data.
- 10:55 Final clean re-compile of all 13 scratch modules in dependency order (lean -R scratch src,
  standard linter set on; LEAN_PATH = scratch oleans + `lake env`): zero errors, zero warnings, zero
  info. No `lake build`; nothing written under `.lake`; nothing registered in the root aggregate.
  Open (not delivered): the rebased `hRP` form with ¬CapWindowPoint at the recentre point (review G).
