# Local first variation

## State — 2026-07-10

`FamilyLocal.lean` removes the global-integrand regularity mismatch from the
moving-volume first-variation API.

- `exists_time_retract` globalizes any open time neighborhood by a smooth map
  `ρ : ℝ → ℝ` whose image remains in that neighborhood and whose germ at the
  chosen interior time is the identity.
- `first_var_local` takes joint spacetime smoothness only on that open time
  neighborhood.  It composes the integrand with `ρ`, obtains the existing
  `FunctionRegularAt` interface from `contMDiff_partial_deriv_fst`, applies the
  established global first-variation theorem, and transfers the result back by
  germ equality.

The proof reuses the project-native partial-time-derivative smoothness theorem;
it does not add a second integration theory or assume a derivative formula as
an input.  Focused verification passed without `sorry`.

## Role in Perelman noncollapsing

This closes the integration-side localization brick needed to consume
`IsHeatPotOn` / `IsConjHeatOn`.  The conjugate-heat existence theorem remains
unproved (0%); this is a completed supporting API brick, not existence
progress by itself.  Dedicated Perelman analytic machinery remains roughly
20–25%, while the Perelman no-local-collapsing endpoint itself remains 0%.

The high-level entropy consumer is not yet checked.  Its honest route needs the
new `laplacianAt_eq_delta` producer, but refreshing that module currently
reaches a deterministic elaboration wall in the pre-existing
`nablaRSFun_eval_moving_raw` theorem.  Raising the heartbeat budget and one
narrow helper extraction both failed at the same model-evaluation block.  This
is an upstream verification/performance blocker, not a missing assumption in
`first_var_local`.

## State — 2026-07-16

`first_var_joint` now localizes both inputs of the moving-volume formula. From
joint smoothness of the metric chart-Gram entries and the scalar integrand on a
single open time neighborhood, it applies `exists_time_retract` once, builds
retracted metric and integrand families, and obtains the existing
`MetricFamilyRegularAt` / `FunctionRegularAt` packages globally in time.

The metric argument keeps each chart component on its actual trivialization
base set. Composition therefore uses `ContMDiffOn.comp` on
`univ ×ˢ baseSet`, not a fictitious globally valid frame. The project-native
`timeDeriv_smoothAt` theorem supplies joint continuity of the retracted Gram
time derivatives. Germ equality then transfers the integral path, integrand
time derivative, metric trace, and base-time measure back to the original
families. No `HasLocallyConstantChartAt`, global-frame choice, derivative
formula assumption, or whole bundle-valued equality was added.

Focused verification and the targeted module build passed without a local
`sorry` or warning from this file.

Honest accounting: `first_var_joint` is proved (100%), and the dedicated
integration-side first-variation localization machinery is complete (100%).
The Perelman no-local-collapsing endpoint remains unstated/unproved here (0%);
its broader entropy/noncollapsing machinery is roughly 53%, and the whole HCG
compactness project remains roughly 60%.
