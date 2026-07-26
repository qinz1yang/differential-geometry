# SecondOrderBootstrap.lean

## 2026-07-19 created (option-1 lane, brick R1a)

First brick of the option-1 route for the Route B packing-radius frontier (see
`Geometry/Comparison/VOLUME_COMPARISON_PLAN.md`, 2026-07-19 entries): the
regularity bootstrap for a *given* solution of an autonomous second-order ODE.

- `contDiffOn_ode2`: on an open `J ⊆ ℝ`, if `y` differentiates, `deriv y`
  differentiates with `(deriv y)' = F (y, deriv y)`, the orbit
  `t ↦ (y t, deriv y t)` stays in `V`, and `F` is `C^∞` on `V`, then `y` and
  `deriv y` are `C^n` on `J` for every `n : ℕ`.  Induction via
  `contDiffOn_succ_iff_deriv_of_isOpen`.
- `contDiffOn_ode2_inf`: the `C^∞` packaging.

Statement deliberately uses a general `F : E × E → E` (weakest form) rather
than the Christoffel-bilinear `Γ`-shape; the chart geodesic equation
`y'' = -Γ(y)(y',y')` is the intended instance via `F (q,v) = -Γ q v v`.

Route source: adapted from the reference route in frenzymath/Poincare-Conjecture
`MorganTian/PoincareLib/Ch01/GeodesicRegularity.lean`
(`contDiffOn_secondOrderODE`), generalized from bilinear-CLM RHS to arbitrary
smooth RHS; statement rewritten in house conventions, no proof body copied
beyond the standard induction skeleton.

Verification: focused check PASSED (no warnings, no `sorry`).  One iteration:
`∞` is scoped notation — `open scoped ContDiff` required (known idiom).

Not added to the root umbrella `DifferentialGeometry.lean`: sibling leaf files
in `Analysis/ODE/` (`SecondOrderGronwall`, `PhaseFlowExistence`, …) are not
listed there either; consumers import this module directly.

Intended consumer (next brick R1b): chart-reading `C^n` regularity of curves
satisfying `HasGeodesicEquationAt` on an open time window inside one chart,
then chaining across charts (`geo_eqOn_of_init` pattern) toward global-in-`t`
regularity of intrinsic radial curves (removes the `expMapC2Radius` cap that
blocks `localPack_card`).
