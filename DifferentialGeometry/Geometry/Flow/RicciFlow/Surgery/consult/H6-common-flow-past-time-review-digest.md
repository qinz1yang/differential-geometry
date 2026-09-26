# Review H6 (single statement: brick CF, common flow past the base time, route (B)), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-h` @ 9f9b7d94d (`DESIGN_C2_ASSEMBLY.md` §3, §5.3), not
compiled. Overall: **CF's signature is mathematically OK; route (B) must fix the post-surgery value at
event times and re-run the cross-event gluing, not merely enlarge the original common flow's time domain.**

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| (a) extension and the equation | OK, re-glue | With `k := activeStage t` take `t < t₁ < stageEndTime k`; keep the ball `U` and the tracing maps, use `closedPrefixAt` (`Surgery/Topology/HistoryRestriction.lean:192`) up to `t₁`, re-run the construction of `exists_backwardSurvivorIncoming_isSolutionOn` (`HistorySurvivorIncoming.lean:196`), restrict to `[a, t₁]`. `IsSolutionOn` is inherited, and the stage metrics, curvature bounds, terminal metric and compact neighbourhood on the original window are preserved. No curvature bound is required on `(t, t₁]` (CF's signature asks none). Gluing "by metric equality at `t`" alone does not deliver smoothness. |
| (a) σ-compactness | OK, existing | `letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp (isSigmaCompact_of_isOpen ThreeModel U.isOpen)` (`Topology/SigmaCompactOpen.lean:11`); the original common-flow proof already uses it for survivor open sets. |
| (b) event times | FIX: pre/post-surgery | `activeStage_at_time` (`HistoryRestriction.lean:45`) gives `activeStage (time k) = k`; non-final `stageDomain` is `Ico`. So at an event time the leaf takes the START of the post-surgery stage, not the pre-surgery end of the old slab; `hball` gives regular backward tracing on all of `U`, so glue across the seam and extend forward on the new stage; `time k < t` need not be assumed. Only `t = horizon` goes through H5 first. `extendHorizon` (`TowerInductionStep.lean:440`) cannot extend an intermediate incoming stage; the pre-surgery value is a different interface. |
| (c) G1d | consistent | The original flow with `D = closed a t` has `lRegularizedDomain S t p Z = ∅`; after the extension `a = t − r² < t < t₁` puts `t` in the new `D.regular`. G6 must be applied to the NEW flow and the curve identified by history-geodesic uniqueness; do not claim the old and new single-flow `lRegularizedDomain`s coincide. |
| (d) counterexample | refutes only "G6 without extension" | Event-free static flat 3-torus, `horizon = 2`, `t = 1`, `r = 1/2`, `a = 3/4`: `hball` holds, but the common flow on `[3/4, 1]` has empty base-time domain, so G6's `σr ∈ lRegularizedDomain` is impossible; on `[3/4, 3/2]` the obstacle disappears. |

Decision: proof lane CF with route (B) exactly as corrected: `t < t₁ < stageEndTime (activeStage t)` for
`t < horizon` (the `Ico` stage domain makes this available at event times too), re-run the survivor-incoming
construction with the longer closed prefix, restrict; `t = horizon` deferred to H5 (X1–X3).
