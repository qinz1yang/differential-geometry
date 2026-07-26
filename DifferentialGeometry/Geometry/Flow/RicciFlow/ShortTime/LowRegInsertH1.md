# LowRegInsertH1

This file is the low-regularity producer for the cancellation-preserving
insertion background difference in the order-zero DeTurck coefficient.

Proved source facts (verification pending the shared Lean slot):

- `connSec_h1`: the moving-to-frozen connection-difference section is bounded
  in intrinsic `H1` using only the metric perturbation `H2` jet;
- `kappaDiff_h2`: the exact lowered-connection background difference is
  bounded in `H2` using only the same lower jet;
- `insert_h1`: after the exact `nins_diff` and `insert_diff` refolds, the full
  two-slot insertion difference is bounded in `H1` by a function of the lower
  `H2` radius alone.

The important mathematical point is that no self-background `H3` arm is
estimated separately.  It cancels before norms are taken.  The source route
is complete; focused Lean verification and any elaboration repairs remain.

Endpoint impact: this supplies the previously missing low-only insertion
piece of the cancellation-preserving order-zero coefficient estimate.  It is
machinery, not yet a proof of `ricci_flow_unif_existence`.
