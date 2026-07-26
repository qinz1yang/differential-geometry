# EdgeRicciAABound

## Scope

This file handles only the six connection-difference-quadratic arms
`ricciAAKer` / `ricciAAArm` in the closed-edge Ricci--DeTurck slope.  It does
not estimate the derivative Ricci arm, the DeTurck residual, or the complete
slope, and it does not prove forward uniqueness.

## Source facts

- `ricciAAKer_rfns` bounds the six-arm kernel by
  `94 * d^3 * RFNS(connDiffSection)^2`.  The constant `94` is the exact
  repeated two-subadditivity cascade `4, 10, 22, 46, 94`.
- `ricciAACoeff_rfns` composes that kernel with the uniformly bounded moving
  four-trace and the first-derivative connection-difference estimate.  It
  uses only `nabla P`, with no higher spatial derivative.
- `ricciAA_path_le` is parameterized by an arbitrary positive budget `eta`.
  On the genuine segment `P = s W`, the energy contribution is
  `O(delta^2) * ||nabla W||^2`, so a carrier-dependent positive radius makes
  it at most `eta * ||nabla W||^2`.
- The local finite permutations and six arm aliases merely expose the body
  of the public `ricciAAKer`; no new tensor representation or foundational
  instance is introduced.
- There is no `sorry`, `admit`, or new axiom in this file.

## Rejected routes

1. A fixed `1/8` budget was rejected as the public producer shape.  Existing
   principal, DA, order-one Ricci, and DeTurck budgets cannot all be added
   faithfully with hard-coded fractions; the AA arm must accept a budget
   chosen by the downstream joint estimate.
2. The existing coarse order-zero Ricci coefficient envelopes were rejected
   because they include the derivative-of-connection-difference arm and
   therefore require an inadmissible second derivative of the arbitrary edge
   difference.
3. The generic `ricciArmOrder0AACommCoeffField` was rejected because it is a
   different commutator coefficient, not the concrete six-arm field in the
   closed-edge slope.

## Verification state

The source derivation and a separate static constant/import audit are
complete.  No Lean check has yet been run because verification in the shared
workspace is serialized by the parent lane.  This file is therefore
**unverified source**, not a proved producer, until its focused check passes.

Endpoint accounting is unchanged:

- `ricci_flow_forward_unique`: 0% (exact theorem not proved).
- `ricci_flow_unif_existence`: unaffected by this file.
- `extends_of_rmBounded`: still depends on both missing endpoint theorems.
