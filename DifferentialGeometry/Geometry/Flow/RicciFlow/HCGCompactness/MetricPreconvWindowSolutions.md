# MetricPreconvWindowSolutions.lean

## 2026-06-13

Stopped per user request before continuing into refactor work.

Current result: the producer-shape route is mathematically viable through the
main analytic seams, but the final endpoint currently exposes a Lean
elaboration/performance blocker.

Verified before adding the final endpoint: the new file focused-checked with
the following pieces in place:
- `SolCovData`, `SolLipData`, and `SolSwapData`;
- `covZeroBdd`;
- `covBddAllSol`;
- `hgLip0Sol`, using `hevComp_of_solutions (N := 0)`;
- `hgLipFinSol`, taking the finite maximum over orders `a <= p`.

Added after that verified point:
- `SolLip0Data`;
- `SolLowData`;
- `denseIccSeq`;
- `winGInfOfSol`, the intended `windowGInf` assembly theorem.

Current blocker: focused checking the file times out at the declaration of
`winGInfOfSol`, at `whnf`, even after bundling the heavy swap, zero-order
Lipschitz, and lower-bound inputs and increasing the local heartbeat ceiling.
The timeout is at theorem elaboration/normalization rather than a mathematical
counterexample or failed proof obligation.

Interpretation: this is likely a refactor/business issue around endpoint
statement shape.  The next clean step is to reduce the public endpoint surface
with a single theorem-facing solution-window data package and/or a named
window-convergence conclusion predicate, then re-export a readable wrapper only
if Lean can elaborate it cheaply.

Verification: final focused check failed on the `winGInfOfSol` timeout.  No
targeted build or axiom checks were run after this blocker.

## 2026-06-17

Attempted the compact-endpoint refactor requested for the P3 window convergence
route.  The producer chain remains mathematically unchanged:
`denseIccSeq` -> `hgLip0Sol` -> `hgLipFinSol` -> `covBddAllSol` -> `windowGInf`.

What was tried:
- a `SolWindowData` package carrying the solution-side hypotheses;
- a compact `WindowMetricPreconvConclusion` wrapper;
- Prop, structure, and inductive conclusion shapes;
- `Classical.choose` instead of eliminating existential proofs into `Type`;
- storing the raw `windowGInf` existential versus storing the exact
  `windowGInf` application;
- structure and single-constructor inductive variants of `SolWindowData`;
- explicit and inferred implicit-argument annotations.

Current blocker: focused checks still fail at elaboration/normalization for the
new compact endpoint.  The reduced failures are now localized to two spots:
the `SolWindowData` binder type and the final constructor argument carrying
the `windowGInf` output.  This is a Lean performance/API-shape blocker, not a
mathematical obstruction and not a missing producer hypothesis.

Smallest next API move: refactor `MetricPreconvWindowGInf.lean` so the abstract
endpoint itself exports a named, already-checked output package, for example a
`WindowGInfOutput`/`WindowGInfConclusion` theorem returned directly by
`windowGInf` or by a sibling theorem proved next to it.  Then
`MetricPreconvWindowSolutions.lean` should consume that named output constant
instead of asking Lean to compare the expanded
`metricDerivNormSupOn` existential at the solution-wrapper boundary.

P4 boundary: the source-domain/pullback layer is still deliberately out of
scope for this pass.  After the P3 wrapper checks, the next separate bridge is
to produce `SourceDomainMetricData` and `SourceMetricCPConvOnWindow` from the
fixed-manifold window convergence plus pullback formulas.

Verification: failed.  The focused check reaches the compact endpoint and
times out at the binder/final-output normalization described above.  No
targeted build or axiom check was run after this blocker.

## 2026-06-17 follow-up

Resolved the endpoint-shape blocker by moving the named output boundary into
`MetricPreconvWindowGInf.lean` and consuming that boundary here.

What landed:
- `winGInfOfSol`, the long-argument flow-instantiated P3 endpoint, now returns
  `WindowGInfOut` rather than the expanded final existential;
- `SolWindowData`, the compact input package for the solution-side hypotheses;
- `WindowMetricPreconvConclusion`, a compact Type-level conclusion package
  carrying the named `WindowGInfOut` proof;
- `winGInfOfData`, the compact-data endpoint, built by destructing
  `SolWindowData` and calling `winGInfOfSol`.

The producer chain is unchanged:
`denseIccSeq` -> `hgLip0Sol` -> `hgLipFinSol` -> `covBddAllSol` ->
`windowGInfOut`.

Verification passed: focused check and targeted module build succeeded.  The
new endpoints are axiom-clean with the expected project axioms only.

Remaining boundary: this completes the P3 fixed-manifold window convergence
wrapper.  The P4 source-domain/pullback layer remains separate: produce
`SourceDomainMetricData` and `SourceMetricCPConvOnWindow` from the
fixed-manifold window convergence plus pullback formulas.
