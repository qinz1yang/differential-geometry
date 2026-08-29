# CostParam

## Status

Focused verification passes without warnings.  The Lean file contains no
`sorry` or `admit`.

## Checked producers

- `lRegLag_time_cont` proves joint continuity of the regularized Lagrangian in
  terminal forward time and square-root backward time for one fixed global
  `C¹` curve, on the regular region.
- `lRegTime_nhds` proves that regularity of a compact square-root-time segment
  persists for all terminal times in a neighborhood.  This is derived from
  compactness and openness of `D.regular`.
- `lRegAction_T_cont` proves continuity of a fixed competitor's regularized
  action as terminal forward time varies.  Its proof supplies a uniform local
  bound on the compact time/curve-parameter rectangle and applies dominated
  convergence.
- `lCost_lt_T_event` is the first L-cost parameter theorem: if `Tn → T` and a
  fixed positive-time `C¹` competitor at `T` has action strictly below `A`,
  then eventually the costs at `Tn` are below `A`.  It derives nearby
  regularity, carrier containment, and the cost bound through
  `lRegCostC1_le`; it does not assume continuity or upper semicontinuity of
  L-cost.

## Exact remaining frontier

The joint theorem tentatively named `lCost_lt_param` is not yet stated or
proved (0%).  Its missing coordinate is the source/base point.  For
`x_n → x`, the next producer must choose a short chart head `[0,c]`, replace
the chart representation of a fixed competitor there by

`u₀ + timeH1.rampDown c (extChartAt I x x_n - extChartAt I x x)`,

and leave the tail `[c,√t]` unchanged.  The required proof obligations are:

1. compact chart-buffer containment and uniform convergence of these heads;
2. convergence of their head actions via `lAction_h1_lim`;
3. C¹ density after joining the perturbed head to the unchanged tail;
4. the resulting fixed-terminal-time source-event cost inequality.

After that fixed-`T` source theorem is checked, combine its connector with
`lCost_lt_T_event` while using `lRegTime_nhds` to keep the same competitor
regular for varying `T`.  Endpoint variation can then reuse
`lCost_lt_event`.  Varying backward time is a later interval-endpoint bridge
and is not needed for the first compact fixed-positive-`tau` reduced-volume
lower-semicontinuity input.

## Progress accounting

- `lCost_lt_T_event`: 100% theorem, 100% dedicated machinery.
- `lCost_lt_param`: 0% theorem; dedicated joint-parameter machinery about 30%.
- fixed-positive-time joint `(T,x)` L-cost upper semicontinuity: about 35%.
- `redVolume_lsc`: 0% theorem; this work supplies only its first analytic cost
  parameter input.
- `redVolume_unif_low` and `smooth_nlc`: 0% theorems.
- whole Perelman L-geometry plan: approximately 45%; whole P2 compactness
  program: below 1%.

## Placement

This is a new native `DifferentialGeometry` module.  It reuses
`CostContinuity`, metric/scalar spacetime continuity, compact thickening, and
the native direct-method cost comparison.  The Ricci-flow references were used
only for the mathematical route; no reference tree is imported or edited.
