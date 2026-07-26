# KochLammFluxPiece

## Intended facts under focused verification

- the directional terminal first-derivative kernel on a selected far spatial
  piece inherits the dual-root factor
  `norm w * exp(-k^2/8) * klFluxTailC * klLpScaleR R`;
- a selected piece contained in one radius-`R` source ball inherits the
  inverse-scale `KLSource1.late_lp` factor;
- joint space-time Holder cancels the two exact radius scales and bounds one
  piece by
  `norm w * exp(-k^2/8) * klFluxTailC * A_p`.

Once verified, this is the input for the same disjoint finite-cover,
annular-shell, absolute-series, and full-potential identification ladder used
by the ordinary terminal source.

The exact theorem `ricci_flow_forward_unique` remains **0%**.
