# HarmonicGauge

## Source status

`hmf_inverse_DT` is source-written and awaits focused elaboration after the
current named export.  The file contains no placeholder, axiom, opaque
producer, new class, instance, or notation.

## Geometric closure

The theorem takes an actual diffeomorphism-valued harmonic-map heat-flow
family from a Ricci-flow metric to a fixed background and proves that pulling
the Ricci flow back by the inverse family satisfies the Ricci--DeTurck PDE on
the same open time window.

The proof composes four already explicit geometric facts:

1. `hmf_neg_gauge` rewrites harmonic-map heat flow as the negative
   pushed-forward source DeTurck field;
2. `push_deTurckVF` identifies that target field with the DeTurck field of the
   inverse-pulled metric;
3. `symm_gauge_vel` gives the positive velocity of the inverse family;
4. `ricci_pullback_DT` differentiates the pulled-back Ricci-flow metric.

No sign or naturality identity remains hidden in an existence hypothesis.

## Remaining analytic frontier

This theorem deliberately does not assume away or claim harmonic-map
heat-flow existence.  The exact forward-uniqueness endpoint still needs a
uniform short-window HMF solver for an arbitrary endpoint Ricci flow, its
initial-edge regularity and diffeomorphism persistence, and then local
Ricci--DeTurck uniqueness plus continuation across the common interval.
Consequently `ricci_flow_forward_unique` remains 0% until those producers are
proved and focused-verified.
