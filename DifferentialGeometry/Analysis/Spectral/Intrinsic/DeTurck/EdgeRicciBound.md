# EdgeRicciBound

## Scope

This file handles only the derivative-only part `ricciDAArm` of the
order-zero Ricci connection-difference coefficient.  It does not claim the
full `edgeRate0` estimate and it does not prove forward uniqueness.

## Source state

- `ricciPart_bds` gives pointwise zeroth- and first-covariant-derivative
  bounds for the exact partner `ricciDAPart`.
- The bounds use one relative inverse-metric insertion, so both squared fibre
  bounds retain `delta^2`.  Only `W` and `nabla W` occur.
- `ricciBase_l2` bounds the rotated lowered connection difference consumed by
  `ricciDA_green` using the public connection-difference fibre estimate and
  `connLow_rfns`.
- `ricciDA_path_le` specializes to the genuine segment `P = s W` and absorbs
  the exact `-2` multiple of the DA pairing into one eighth of the Dirichlet
  energy plus `K * ||W||^2`.
- There is no `sorry`, `admit`, or new axiom in this file.
- The tensor-symmetry step is proved locally by extensionality.  This avoids a
  declaration with the same purpose that lives outside the file's import
  closure and avoids adding a heavy downstream import.

The source derivation is complete, but no Lean check has yet been run.  The
shared workspace is currently using serialized Lean verification, so this
file must remain classified as **unverified source**, not as a proved
producer, until its focused check passes.

## Failed or rejected routes

1. Reusing `edgePairMono` was rejected: it contains two moving traces and has
   the wrong scaling.  The Ricci derivative cancellation leaves one moving
   trace.
2. Estimating `ricciDAArm` before pairing was rejected: it exposes a
   derivative of the connection difference and would require an inadmissible
   second derivative of the arbitrary edge difference.
3. A proposed cancellation with the complete order-one coefficient was not
   used.  Its five connection-action placements do not exactly match the two
   DA flux monomials; separate low-order estimates are the faithful route.

## Remaining adjacent frontier

After the exact split

`linearizedRicciConnDiffOrder0CoeffField = ricciAAArm + ricciDAArm`,

the `edgeRate0` term still contains the non-derivative `ricciAAArm` and the
Riemann half contribution.  The latter must be combined with the concrete
refold output; an existential generic `C0` family cannot be treated as a
uniform reaction coefficient without its producer bounds.  `edgeRate1` also
still needs its concrete low-order bound.

Endpoint accounting remains unchanged:

- `ricci_flow_forward_unique`: 0% (exact theorem not proved).
- `ricci_flow_unif_existence`: unaffected by this file.
- `extends_of_rmBounded`: still depends on both missing endpoints.
