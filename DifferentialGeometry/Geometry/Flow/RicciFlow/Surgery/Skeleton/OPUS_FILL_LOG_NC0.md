# NC0 fill log

Brick NC0: parabolic kappa-noncollapsing passes to the terminal (closed-end) time.

## Delivery

File: `DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/Noncollapsing/TerminalTime.lean` (170 lines, new,
not wired into `DifferentialGeometry.lean`).

- `FlowMetricBall.isKappaNoncollapsed_of_forall_time_lt`: for `S : SolutionOn D` with `IsSolutionOn S` and
  `interior D.carrier ⊆ D.regular`, if every `FlowMetricBall` at a time `t < T` with radius `≤ ρ` that is
  `IsParabolicallyRmControlled` is `IsKappaNoncollapsed κ`, then so is every such ball at time `T`.
- `parabolicallyKappaNoncollapsedBelowScale_of_forall_time_lt`: with `D.carrier ⊆ Iic T` and `0 < ρ`, the same
  hypothesis gives `ParabolicallyKappaNoncollapsedBelowScale S κ ρ`.

Predicate: the tree's `FlowMetricBall.IsParabolicallyRmControlled` / `IsKappaNoncollapsed` /
`ParabolicallyKappaNoncollapsedBelowScale` (`Perelman/Noncollapsing/Parabolic.lean`, `Defs.lean`), the one that
`AncientPointedFlowLimitNoncollapsing.lean` produces. `ancientTimeInterval` satisfies
`interior (Iic 0) = Iio 0 = regular` and `carrier ⊆ Iic 0`, so the corollary applies to the limit with no adapter.

## Route

For `δ ∈ (0, 1/2]`: `s = T − r²δ²`, `a = n²δ²`, `R = r(1−δ)`, `r' = e^{−a}R`.
`inner_le_exp_mul_inner_of_rmNormSq_le` on the curvature slab gives `e^{−2a} g(T) ≤ g(s)` on `B_T(x, r)`;
`riemannianEDistOf_le_of_metric_lower_on_ball` gives `B_s(x, r') ⊆ B_T(x, r)` (no completeness needed);
the window `[s − r'², s] ⊆ [T − r², T]`; the kappa test at `s` plus
`riemannianVolumeMeasure_le_exp_mul_of_rmNormSq_le` give `κ r'ⁿ e^{−n³δ²} ≤ vol_T(B_T(x, r))`; `δ_k → 0`
with `le_of_tendsto'`.

## Verification

- `lake env lean` (2 threads): clean, no warnings.
- `#print axioms` (scratch copy, removed): both theorems `[propext, Classical.choice, Quot.sound]`.
- `#lint` (scratch copy): 0 errors, 14 linters.
- Header: follows the sibling files (imports first, no copyright header / module docstring), as in
  `VolumeDistortion.lean`.
