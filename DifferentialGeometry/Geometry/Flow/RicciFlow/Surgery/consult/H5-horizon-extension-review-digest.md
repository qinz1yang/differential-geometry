# Review H5 (single statement: bricks X1–X3, horizon extension leaves the reduced volume unchanged), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-h` @ 9f9b7d94d (`DESIGN_C2_ASSEMBLY.md` §1(b), §5.4).
Overall: **the X1–X3 repair is mathematically valid, but it lives at the `RetainedCoreHistory` level;
"the extended history stays in `InCutoffClass`" is FALSE.** X2 must be proved from the variational
definition on the original absolutely continuous curves, not by comparing old and new `historyLExp`.

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| (a) X1 extension / class | extension OK; class FALSE | `InCutoffClass` (`Surgery/Topology/CanonicalNeighborhoodInduction.lean:165`) contains `H.time (Fin.last H.eventCount) = H.horizon`; keeping events and the schedule while strictly raising the horizon breaks it; keeping records ≠ keeping the class. The auxiliary history need only be a `RetainedCoreHistory` and supply §5.4's `hagree`. Non-degenerate last slab: G1 (`exists_isSolutionOn_extension_past_right_endpoint`, needs its compactness, joint smoothness and Ricci equation inputs); degenerate case: start from G0 (`exists_closedSlab_of_metric`). The design's statements (`exists_extendHorizon_gt`, `reducedVolume_extendHorizon`, …) are already at that level: no change. |
| (b) X2 endpoints, cost, density | OK, not a global `rfl` | `regularizedCost` refers to the horizon indirectly (`stageEndTime`, time-legality of competitors, `regularizedStageStart`); the old base time `T ≤ h ≤ h'` gives `min(T,h) = min(T,h') = T`, so the reversed start of the last segment is the same zero and the other segments' clocks are unchanged. Compare actions along the SAME curve via `hagree`, keep the `old/oldOutput` competitor conditions in the cost and the `RegularCrossing` condition in the minimal-endpoint set: competitor action sets, infimum, minimal endpoint set and density coincide; the endpoint metric on the effective window coincides; so each `B`-integral and hence the `limsup` coincide, with NO limit/integral interchange. Out-of-range parameters allowed by the signature need the empty-competitor / zero-density branches handled separately; do not claim the endpoint measures are always equal. |
| (c) X3 terminal clause | OK, return to the old prefix | `TerminalNoncollapsedBefore` (`:196`) inspects `H.extendHorizon T … (G.closedPrefix T …)` for each `T`; with `a < T < s` choose `T < T' < s` and use the SAME `G`'s longer closed prefix; apply the leaf on the auxiliary history at the OLD time `T`, then transfer back to `NoncollapsedBefore … T` on the old prefix via reduced volume, the old metric and `isParabolicallyRmControlledBall` transfer. No class membership of the auxiliary history, no pushing the control clauses to `T'`. |
| (d) counterexample / wrong strengthening | class claim refuted | Any class history strictly extended keeps the old last event time `h` but has horizon `h' > h`. Do not strengthen X2 to "old and new L-exponential domains coincide": the old right endpoint `T = h` is not in the old regular time domain but enters the new one; the existing closed-slab L-domain congruence requires the base time strictly inside. This does not refute the reduced-volume invariance under the original AC definition. |

Closing route: action agreement on the old time window → original minimal endpoints and density agree →
reduced volume agrees → terminal clause on the old prefix. No "extended history stays in the class"
obligation anywhere.

Decision: proof lane X for `exists_extendHorizon_gt`, `stageMetric_extendHorizon`, `reducedVolume_extendHorizon`,
`isParabolicallyRmControlledBall_extendHorizon` and the small `lt_stageEndTime_`/`stageDomain_`/`mem_Ico_`
lemmas of §5.4, exactly as stated, by the reviewed route.
