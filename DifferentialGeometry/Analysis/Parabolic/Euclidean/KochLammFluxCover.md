# KochLammFluxCover

## Intended facts under focused verification

- the directional kernel/source product is integrable on each selected piece
  controlled by one `KLSource1.late_lp` cylinder;
- an arbitrary finite ball cover is disjointized inductively, preserving
  integrability and multiplying the one-piece Gaussian bound only by the
  cover cardinality;
- the resulting bound keeps the exact factor
  `norm w * exp(-k^2/8) * klFluxTailC * A_p`.

This is the finite-cover input for the annular-shell estimate.  The exact
theorem `ricci_flow_forward_unique` remains **0%**.
