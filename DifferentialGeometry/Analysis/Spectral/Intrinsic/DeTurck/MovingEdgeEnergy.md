# MovingEdgeEnergy

## Proved source facts

- `normSq_family_cont` gives joint continuity of the squared norm of a
  continuous `(0,s)` tensor family under a continuous moving metric.  Its only
  metric input is closed-set chart-Gram continuity.  The proof is the genuine
  local inverse-Gram contraction, not a fixed-metric replacement.
- `movingDiffEnergy` is the intrinsic energy of `g1 - g0`, measured using the
  moving carrier `g0` and its volume measure.
- `movingEnergy_cont` derives continuity of that energy on a compact closed time
  set from the two existing chart-Gram `C0` hypotheses.  It introduces no
  endpoint differentiability, curvature bound, or maximal-regularity input.
- `movingMetricReact` records the exact inverse-metric reaction for a moving
  covariant two-tensor norm.
- `deTurckRHS_cont` turns `JointChartGramSmooth` into closed-slab intrinsic
  tensor continuity of the Ricci--DeTurck right-hand side.  Consequently
  `carrierEdge_bounds` supplies one fibre-operator bound for
  `Q = -(1/2) RD(g0)` on the entire closed slab, including time zero.
- `reactInBasis_deriv` identifies every basis-level reaction formula with the
  derivative of the same intrinsic squared norm.  Derivative uniqueness gives
  `reactInBasis_eq` and `movingReact_basis`, so basis independence is obtained
  without unfolding the tensor representation or proving a raw component
  change-of-basis formula.
- `movingReact_ortho`, `ricReactArray_le`, and `movingReact_le` then specialize
  to a moving orthonormal basis and prove the pointwise estimate
  `|reaction| <= 4 n^3 B |W|_g^2`.  Its hypotheses mention only the carrier
  equation and the operator bound for its half-speed; no spatial derivative of
  the arbitrary comparison path occurs.
- `metricTrace_op_le` proves `|tr_g Q| <= n B` from the same fibre-operator
  hypothesis.  `traceTime_rd` identifies the chart-defined volume variation
  trace with `-2 tr_g Q`, and `movingReactVol_le` combines both scalar
  reactions into a single explicit `K |W|_g^2` bound.
- `movingNorm_time` derives the pointwise norm derivative from an interior
  carrier variation `-2Q` and an interior tensor variation `Wdot` by applying
  the generic `hasDerivWithinAt_normSq0S_ricciFlow` theorem.  It requires no
  time derivative at the closed edge.
- `movingNorm_rd` specializes this formula to two genuine Ricci--DeTurck
  equations: `Q = -(1/2) RD(g0)` and
  `Wdot = RD(g1) - RD(g0)`.
- `movingEnergy_deriv` and `movingEnergy_rd` give respectively the general and
  Ricci--DeTurck energy first variations on an open regular time set, including
  the moving-volume trace term.
- `movingRate` names that exact Ricci--DeTurck energy rate.  It contains the
  carrier inverse-metric reaction, twice the RHS-difference pairing, and the
  moving-volume reaction, with no hidden endpoint derivative.
- `movingEnergy_rate` is the open-window derivative theorem in exactly the
  named form needed by the scalar Gronwall lemma.
- `movingEnergy_zero` packages the closed-edge conclusion.  Its geometric
  hypotheses are only joint chart-Gram smoothness on `Ioo 0 T`, joint
  chart-Gram continuity on `Icc 0 T`, the two Ricci--DeTurck equations on the
  open interval, and equality at time zero.  The only remaining analytic
  input is the displayed scalar bound `movingRate t <= K * movingDiffEnergy t`.

These declarations, including the newly added carrier and reaction bounds, are
currently source-complete and contain no
`sorry`/`admit`/axiom.  A focused Lean check is pending the coordinated named
dependency build in the shared worktree.

## Mathematical role

This closes the continuity, exact differentiation, and abstract Gronwall
assembly halves of the initial-edge energy argument.  On the open
positive-time interval the carrier is one Ricci--DeTurck solution.
`EdgeDifferenceEnergy.edgePrincipal_half` supplies the small principal
perturbation, while `EdgeLowerPairing.edgeCore_pair_le` supplies the generic
fixed-time order-zero/order-one estimate once the concrete nonlinear
coefficient fields have been split and uniformly bounded.  Edge continuity,
rather than an endpoint time derivative, closes the final scalar argument.

## Exact remaining analytic obstruction

The moving inverse-metric and volume reactions are no longer part of the
obstruction: both uniform-to-zero coefficients are now obtained directly from
`carrierEdge_bounds`, via `movingReactVol_le`.

The remaining lower-order RHS-difference estimate cannot be obtained merely by taking a compact-time
supremum of the `Ioo`-smooth coefficient fields.  Such a supremum is available
on `[epsilon,T]`, but its constant may diverge as `epsilon -> 0`; continuity of
the energy at zero does not make that version of Gronwall close.  The endpoint
hypotheses therefore still need one of the following genuine producers:

1. the intended edge regularization estimate, deriving a uniform first
   background-covariant derivative bound and a square-root-time weighted
   second derivative bound from chart-Gram `C0`, interior smoothness, and the
   Ricci--DeTurck PDE;
2. an initial-edge reverse maximal-regularity realization giving the required
   `L2_t H^(a+2) intersect H1_t H^a` data; or
3. a complete structural cancellation proving the full nonprincipal energy
   pairing is uniformly lower order without separately bounding the carrier
   jets.

The current source follows route 3 through the already proved principal-arm
identity and the source-complete generic lower-order pairing.  What is not yet
present is the concrete Ricci--DeTurck coefficient split which must show that
the actual RHS difference has those bounded lower arms plus absorbable terms
carrying the small `C0` metric difference.  A fixed-initial-carrier shortcut
was also rejected: its differentiated top coefficient contains uncontrolled
endpoint spatial derivatives and therefore does not improve the edge problem.

## Honest status

- Closed-edge energy continuity machinery: 90% (source written; focused check
  pending).
- Exact moving Ricci--DeTurck energy derivative: 85% (source written; focused
  check pending).
- Carrier scalar-reaction control: 88% (closed-slab carrier bound, intrinsic
  basis-independence, volume-trace identity, and combined pointwise
  `K |W|^2` source written; focused checks pending).
- Generic lower-order pairing and closed-edge Gronwall assembly: 72% (source
  written; focused checks pending).  The concrete nonlinear Ricci--DeTurck RHS
  split and its uniform-to-zero pairing bound remain the analytic frontier
  described above.
- `ricci_flow_forward_unique`: 0% until the exact endpoint theorem is proved and
  verified.
