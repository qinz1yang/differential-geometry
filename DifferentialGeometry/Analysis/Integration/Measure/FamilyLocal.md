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
