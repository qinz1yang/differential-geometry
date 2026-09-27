# X3 — Crossing room on the terminal slab (2026-09-26)

New file `Topology/BackwardTraceDistortionTerminal.lean` (imports only X2's
`BackwardTraceDistortion`). Compiles clean read-only (`LEAN_NUM_THREADS=2 lake env lean`, 0
diagnostics); `#lint` 14 linters clean on a scratch copy; axioms propext/choice/Quot.sound. Route: direct, not a reduction to the event case (a terminal
slab is not an event slab of any history with the same records; no cut event exists there).

Stated for any `RetainedCoreHistory H` with `h : H.time last < H.horizon` and
`activeStage t = Fin.last`; the crossing leaf applies them to
`K = H.extendHorizon T _ (G.closedPrefix T _ _) hG` (as `TerminalNoncollapsedBefore` does), with
`(K.finalSlab h).flow = (G.closedPrefix T ..).flow`; `activeStage t = last` from the new
`ObservedHistory.activeStage_eq_last_of_time_last_le`. OPEN for the consumer: the conclusion is
`K.CapWindowPoint` with records `(records i).extendHorizon ..`; moving it to `H.CapWindowPoint` is
NOT `Iff.rfl` (`BackwardPointTrace K.toHistory` and `BackwardPointTrace H.toHistory` are different
types) and needs a trace transport along `extendHorizon` (same stages/events), not written here.

Slab-dependent glue replaced: current-slab metric comparison now from `finalSlab h` (private
`initialMetric_inner_le_exp_of_normSq_le_of_eq_last`); trace |Rm|² bound with `hlast`/`hfinal`
instead of `hne` (private `normSq_stageMetric_le_of_backwardPointTrace_of_final`); gradient ball
bound from `finalSlab h`. X2's constant conditions unchanged.

Duplicates for the lead to merge: the private core
`exists_cap_capture_of_ball_point_without_trace_of_comparison` is X2's main proof generalised to any
current stage (takes `hlast`, `hcurrent`, `hfinal` and the current-slab comparison `hcmp`); X2's
event theorem is the `hcmp := initialMetric_inner_le_exp_of_normSq_le hi` instance, so both files
can share it. `normSq_stageMetric_le_of_backwardPointTrace_of_final` generalises X2's private
`normSq_stageMetric_le_of_backwardPointTrace` (hne ⇒ hlast/hfinal). X2's private helpers are used
via `open private`, not copied.
