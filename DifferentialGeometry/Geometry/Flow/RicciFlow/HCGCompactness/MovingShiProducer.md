# MovingShiProducer

## Result

`movingShiBoundSol` turns a uniform squared-norm bound on `Rm` for a
dimension-three Ricci-flow solution into one constant controlling the moving
Ricci covariant-derivative tower through order three on an interior tail.

The construction chooses an interior time `t0`, translates it to zero, and
keeps the translated larger interval whose left endpoint is negative. This
lets `towerHeatSol` cut exactly at zero while `towerNorm_joint` supplies
continuity at the closed slab endpoint. `BernsteinTower.estimate_of_heat`
controls the Riemann tower; `ricTower_normSq_le` contracts it to the Ricci
tower; an explicit four-term maximum makes the bound uniform in orders
zero through three.

## Status

`movingShiBoundSol` and its dedicated machinery are **100% complete**. The
file is warning-free under focused verification and exported by a targeted
build. Its axiom closure, together with `towerHeatSol`, `towerNorm_joint`,
`BernsteinTower.estimate_of_heat`, and `ricTower_normSq_le`, contains only
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx`.
`ExtendShiInputs.movingShi_of_soln` has been wired to this producer; its
downstream-file verification is pending only a missing Spectral `.olean`
refresh, not a mathematical proof obligation.

## 2026-07-14 arbitrary-order strengthening

`movingRmBoundSol` now proves the corresponding Riemann-tower estimate through
any prescribed finite order on any prescribed interior tail. It chooses one
constant for all `k <= order` by taking a finite supremum of the individual
Bernstein constants. `movingShiBoundSol` is now a short order-three corollary,
followed by `ricTower_normSq_le`.

`rm04_bound_can` also lives in this lower producer module: it converts a bound
for any realizing `(0,4)` curvature field into the canonical intrinsic
curvature bound consumed by `movingRmBoundSol`.

`movingRmBoundSol`, `movingShiBoundSol`, and their dedicated machinery are
**100% complete**. Focused verification and the targeted module build passed;
the fresh axiom-closure check for the strengthened theorem is pending the
active shared Spectral rebuild.

The public arbitrary-order Ricci form is `movingShiBoundN`. It contracts the
Riemann-tower estimate order by order and takes one finite supremum, while
`movingShiBoundSol` is now only its order-three compatibility corollary.
`movingShiBoundN` passed focused verification and its targeted export build.
