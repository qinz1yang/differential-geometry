# B6a — all-radii, all-depths pointed limit by diagonalization (2026-09-26)

- Read AGENTS.md, NAMING §2–6, Skeleton/README, DESIGN_CROSSING (B6a/B6b), IncompleteLocal.lean,
  TracedTerminalCompactness.lean (:168, :265, :1574, :1886, :1959), LocalCurvatureInjectivity.lean,
  MetricAgreement.lean, BallImage.lean, OpenExhaustion.lean, AncientGluing.lean.
- Finding: IncompleteLocal is spatial only (Riemannian, radius `< rho`); no flow data. The
  complete-case all-radii theorem already exists
  (`exists_canonical_metric_compact_limit_with_source_geometry_of_local_curvature_injectivity`,
  LocalCurvatureInjectivity.lean:155). So the spatial diagonal is: complete extensions on balls of
  radius `n+1` along a subsequence (LocalCompletion), complete-case limit, metric change back.
- Finding: the flow diagonal needs no new PDE: `exists_common_compatible_solution_subsequence_on_open_sets_and_intervals_of_terminal_convergence`
  (OpenExhaustion.lean:21) takes per-index intervals, and `exists_ancient_solution_of_compatible_open_cover`
  (AncientGluing.lean:17) glues `[-(n+1), 0]` pieces on a monotone exhaustion into `(-∞, 0]`.
- Plan: file 1 `Pointed/Compactness/CompactBalls.lean` (spatial, generic); file 2
  `Surgery/Topology/AncientPointedFlowLimit.lean` (flow limit, stated for a generic sequence of
  pointed manifolds carrying local solutions on neighbourhoods of the balls with jets; the
  history-specific producer of those local solutions is B6b's).
- 2026-09-26 (+~1h) File 1 `Geometry/Compactness/CheegerGromov/Pointed/Compactness/CompactBalls.lean`
  compiles clean (read-only `lake env lean`, no output): `exists_pointed_convergence_of_eventually_compact_balls`
  (connected slices) and `exists_pointed_convergence_on_base_components_of_eventually_compact_balls`
  (base components, `liftTargetOpen`, the shape the terminal slices need). Output: complete connected
  limit, canonical `MetricConvergenceData`, and eventual capture of every closed ball. Next: file 2,
  the ancient flow limit.
- 2026-09-26 (+~2h) File 2 `Surgery/Topology/AncientPointedFlowLimit.lean` done.
  `exists_ancient_flow_limit_of_pointed_convergence_of_local_solutions` (given a spatial pointed
  convergence with complete connected limit, and for each `k` eventually a local solution `h k n` on an
  open `W k n ⊇ B̄(xₙ, k+1)` on `[-(k+2), 0]` with `h k n 0 = gₙ|W`, all-order curvature-derivative
  bounds on `B̄(k+1) × [-(k+1), 0]` and eventual overlap compatibility): one further subsequence `ψ`,
  one ancient solution `G` on `P × (-∞, 0]` with `G 0 = g∞`, and `C^p` convergence on every compact
  subset of `B(y∞, (k+1)/2) × [-(k+1), 0]` of the pulled-back local flows to `G` (exhaustion by
  `OpenExhaustion.lean:21`, gluing by `AncientGluing.lean:17`). Headline
  `exists_ancient_pointed_flow_limit_of_local_solutions`: spatial all-radii limit (file 1, base
  components) + flow limit in one statement; spatial jets are derived from the flow jets at `t = 0`.
- Verification: file 1 in-repo `LEAN_NUM_THREADS=2 lake env lean` clean; file 2 on a scratch
  concatenation (file 1 has no olean) clean; `#lint` (14 Batteries linters) 0 errors on 9
  declarations; all four public theorems: `[propext, Classical.choice, Quot.sound]`. Names unique.
- Not claimed: slice completeness (B6b), bounded curvature (F9), the history producer of the local
  solutions (B2b survivor flows, Shi jets, volume via `NoncollapsedBefore`), root aggregate wiring.
- Placement note: file 2 is generic Ricci-flow compactness; natural home
  `Flow/RicciFlow/Compactness/Limits/`, kept in `Surgery/Topology/` per the lane's file restriction.
