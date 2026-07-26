# StepCStageInjectivity

## 2026-07-18 framed migration: focused and exact green

`HasStageJetData.inj_tail` now uses `framedChartAt` for the source and target
charts.  Its source-domain-to-chart-target bridge is derived from the existing
`expRadiusGp` geometric output through `framedExp_source` and the orthonormal
frame comparison.  The intrinsic buffer, approximate-return, segment, Neumann,
and injectivity arguments are unchanged, and no new assumption or wrapper was
added.  Static source and diff review passed.  After exact-refreshing
`StepCStageReturn` and `StepCSourceBuffer`, this file passes focused Lean
verification against the current canonical framed artifacts.  Its own exact
target refresh also completed successfully in the coordinated Stage-DAG write
chain.

The framed source migration and current module verification are 100%.  The live
`MetricCompactBase.exists_b1_raw` declaration has a complete proof body, but
its canonical framed downstream validation is still in progress.  The
separately named textbook Step B1 theorem and unconditional compactness
endpoints remain theorem-level 0%; dedicated B1 machinery is about 95%,
Chapter 4 machinery about 87%, and whole-HCG machinery about 60%.

## Verified result

`HasStageJetData.inj_tail` is focused-green.  With the same explicit radius
room used by `return_tail`, it proves one rectangular all-pairs tail on which
the actual global `stageComparisonMap` is injective on the retained closed
source ball.

The proof uses the reverse-stage comparison map only as an approximate return
map.  Equality of forward images puts two source points inside one uniform
intrinsic buffer; the normal-coordinate segment then stays in a slightly
larger retained ball, and the order-one stage-map jet estimate plus the
Neumann injectivity lemma identifies the two points.  No exact inverse claim,
whole-cage containment, endpoint-radius assumption, or new compactness input
is introduced.

## Frontier and accounting

- This global-injectivity producer: 100%.
- Stage-map local diffeomorphism, basepoint preservation, return control, and
  global injectivity: 100% as individual producers.
- The live `MetricCompactBase.exists_b1_raw` proof body is complete; current
  framed-chain validation is pending downstream metric/inverse refreshes.
- The separately named textbook Step B1 theorem remains theorem-level 0%.
- Dedicated B1 machinery is approximately 95%; Chapter 4 machinery about 87%;
  whole-HCG machinery about 60%.

The chart-coefficient-to-intrinsic and exact-local-inverse bridges now have
complete downstream proof bodies; their canonical framed revalidation remains
after the Stage-DAG exact chain.
