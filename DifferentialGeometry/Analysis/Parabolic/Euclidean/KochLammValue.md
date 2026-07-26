# KochLammValue

## Proved/source-written fact

`klHeat0` joins the early and terminal halves of the ordinary Koch--Lamm heat
potential at an arbitrary positive observation time. `klHeat0_norm` gives the
full value estimate from the `KLSource0` local `L¹` and late
`L^((n+4)/2)` radii, with no metric-dependent horizon and no cover input.
`klEarly0_int` additionally proves Bochner integrability on the whole early
half-slab, rather than merely bounding a possibly nonintegrable integral;
`klLate0_int` gives the matching terminal-half integrability at `sqrt t`.
`klHeat0_eq_heatPot` then uses the two integrability results, disjoint slab
decomposition, and product Fubini to identify `klHeat0` exactly with the
original interval-integral Duhamel operator `heatPot0`.

The source has no proof placeholder or new assumption. Focused verification is
pending the coordinated short-path dependency export.

## Remaining analytic work

The split potential still needs spatial derivative realization, local
spacetime `L²` gradient bound,
and late `L^(n+4)` gradient bound. The divergence-source value estimate is being
completed separately. The exact theorem `ricci_flow_forward_unique` remains
**0%** until the compact-manifold gauge and Ricci-flow comparison are proved.
