# KochLammFluxShell

## Intended fact under focused verification

Any radius-`R` cover of the `k`-th half-open shell with cardinality at most
`(5(k+1))^dim V` yields the bound

`(5(k+1))^dim V * norm w * exp(-k^2/8) * klFluxTailC * A_p`.

The shell geometry is reused from `KochLammLateShell`; only the directional
flux estimate is new.  This is the summand consumed by the flux Gaussian
series.  The exact theorem `ricci_flow_forward_unique` remains **0%**.
