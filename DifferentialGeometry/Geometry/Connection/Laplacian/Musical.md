# Musical connection-Laplacian bridges

## Scope

This file is the minimal rank-one bridge for realizing a harmonic-map
heat-flow unknown as an existing `(0, 1)` mixed-tensor unknown.  It adds no
class, instance, notation, axiom, or regularity assumption.

## Proved source facts

- `mixed01_connLap`: the mixed `(0, 1)` connection Laplacian evaluated at the
  canonical unit `(0, 0)` tensor realizes exactly the existing cotangent
  connection Laplacian.
- `sharp_connLap`: the Levi-Civita vector connection Laplacian of the musical
  sharp of a smooth one-form equals the musical sharp of its mixed `(0, 1)`
  connection Laplacian.

The proof is intrinsic.  It combines the checked unit-evaluation identity
`tensorSecondCovDeriv_unit_eval_genVal` with the checked metric-compatibility
identity `inverseMetricSharpField_covGrad_eq_zero`, then traces over the same
canonical smooth orthonormal frame used by the three Laplacian definitions.

## Verification state

Source-only implementation is complete.  Per the parent lane's instruction,
no Lean/Lake process was started in this lane; focused elaboration remains for
the integrating lane.  There is no `sorry`, `admit`, or axiom in this producer.

- Exact theorem completion: 0% until the focused check passes.
- Mathematical/proof-source machinery: 100% assembled.

## Downstream effect

This removes the representation-level objection to using a covector
displacement variable for the common DeTurck gauge.  It does not by itself
construct the time-dependent nonlinear harmonic-map heat-flow fixed point,
and therefore does not change the 0% endpoint status of
`ricci_flow_forward_unique`.
