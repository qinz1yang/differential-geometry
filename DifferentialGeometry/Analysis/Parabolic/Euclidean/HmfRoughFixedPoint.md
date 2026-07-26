# HmfRoughFixedPoint

## Durable mathematical content

`HmfFPData` packages three Duhamel arms of an experimental local-addition
rough-path equation on a complete Banach space:

- the noncritical seed;
- the prescribed inverse-domain-metric-difference principal flux;
- the target/local-addition quadratic-gradient source.

`HmfFPData.duh_contracting` gives the exact contraction rate
`4 * eps + K * R` on the radius-`R` state ball.  The factor `4` is the
critical heat-kernel convolution bound proved in `HeatKernelBeta.lean`.
There is no horizon-small factor in this arm.  The horizon may enter only
through the seed estimate `eta <= (1 - rate) * R`.

`HmfFPData.rough_fixed` is a genuine Banach fixed-point theorem for that
abstract Duhamel equation: it returns a unique state-ball solution and proves
that its initial trace is zero.  It is not yet a harmonic-map heat-flow
producer.  In a full-state strong local-addition formula the vertical
derivative multiplying `V_t` should cancel the identical vertical derivative
in the leading tension term, so the prescribed principal coefficient is the
right one.  What this package still omits is the value dependence of the
quadratic/local-addition coefficient and its third difference arm
`(Q(u)-Q(v))(Dv,Dv)`.

## Verification state

Source written while the shared named build was active.  No focused Lean
check has yet been run.  The theorem is therefore not counted as checked
machinery until that build ends and the focused check succeeds.

A static API audit found one definite source-level rewrite defect in
`duh_mem`: after `Metric.mem_closedBall` the goal contains `dist (hmfDuh D u)
0`, so the proof must use `dist_zero_right`, not `dist_zero_left`.  The Lean
file is currently held by pre-existing claim
`db257e88-43dc-4af9-a7aa-84ecc785fcb6`; it has not been overwritten or
force-released.  Consequently any rebuild of this source remains expected to
fail at that line until the owning lane releases or repairs it.

## Remaining geometric realization

This file deliberately does not assume a harmonic-map heat flow exists.  A
faithful strong-equation realization needs:

1. the principal Duhamel estimate with `eps` supplied by the closed-edge
   `C0` smallness of `g(t)^{-1} - g(0)^{-1}`;
2. a full-state chain-rule theorem proving cancellation of the vertical
   local-addition derivative in the top-order term;
3. the value-Lipschitz state-dependent quadratic coefficient, including the
   third arm proved abstractly in `HmfStateQuad.lean`;
4. the noncritical seed estimate on a short horizon;
5. compatibility of the chartwise rough-path carrier and its initial trace.

The state-dependent mass remains mandatory for the finite Galerkin/energy
route, but it need not be inserted into the strong rough formulation after
the cancellation theorem.  The forward Ricci-flow uniqueness endpoint
remains 0% until the faithful realization, gauge PDE identity, and gauge
undoing are all proved and checked.
