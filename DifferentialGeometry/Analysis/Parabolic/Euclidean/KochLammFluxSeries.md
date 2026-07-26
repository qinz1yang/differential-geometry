# KochLammFluxSeries

## Intended facts under focused verification

- `klFluxWeight d k = (5(k+1))^d * exp(-k^2/8)`;
- this exact weight is dominated by a polynomial times `exp(-k/8)`;
- the exact flux shell weight is summable, defining the finite
  dimension-only constant `klFluxSeries d`.

This is the summability input for absolute terminal flux integration.  The
exact theorem `ricci_flow_forward_unique` remains **0%**.
