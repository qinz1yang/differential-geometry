# CostBaseParam

## Status

Focused verification passes without warnings, and the targeted module refresh
passes.  The Lean file contains no `sorry` or `admit`.

## Checked producers

- `chart_head_act_lim` constructs affine `timeH1.rampDown` perturbations on a
  short chart head `[a,c]` and proves convergence of their regularized actions
  using the native `lAction_h1_lim` theorem.  Compact chart-buffer containment,
  uniform convergence, chart realization, and recovery of the original curve
  are proved internally.
- `lCost_lt_x_event` is the genuine source/base-point parameter theorem.  For
  `q n -> x`, it selects a short positive chart head, inserts the ramp-down
  connector from `q n` to the unchanged competitor at `c`, proves head-action
  convergence, joins to the unchanged tail, applies C1 density, and obtains
  `lCost S T (q n) y tau < A` eventually.

Neither theorem assumes continuity or upper semicontinuity of L-cost.  The
implementation reuses `chartTimeH1`, `lAction_h1_lim`,
`exists_chartH1_join`, `lAction_c1_dense`, and `lRegCostC1_le`.

## Joint frontier

The separate checked producers now vary each compactifying coordinate needed
at fixed positive backward time:

- `lCost_lt_T_event` varies terminal forward time with a fixed competitor;
- `lCost_lt_x_event` varies the source point at fixed terminal time.

These two sequential statements cannot by themselves be combined into joint
upper semicontinuity: separate upper semicontinuity does not supply the uniform
terminal-time neighborhood needed for the moving chart-head competitors.  The
smallest honest next producer is joint convergence of the chart-head action
when both the terminal time and the `timeH1` chart representative vary.  Its
proof must extend the compact-buffer dominated-convergence argument underlying
`lAction_h1_lim` to the coefficient times `T_n - s^2`; it must not add a
uniform-continuity hypothesis at the consumer.

Once that analytic producer is checked, the existing proof of
`lCost_lt_x_event` can replace `hheadLim` by the joint head limit and use
`lRegAction_T_cont` on the unchanged tail, yielding `lCost_lt_param`.

## Progress accounting

- `lCost_lt_x_event`: theorem 100%, dedicated machinery 100%.
- fixed-positive-time source-point L-cost upper semicontinuity: 100%.
- `lCost_lt_param`: theorem 0%; dedicated machinery approximately 60%.
- fixed-positive-time joint `(T,x)` L-cost upper semicontinuity: about 60%.
- `redVolume_lsc`, `redVolume_unif_low`, and `smooth_nlc`: each 0% theorem.
- whole Perelman L-geometry plan: approximately 45%; whole P2 compactness
  program: below 1%.
