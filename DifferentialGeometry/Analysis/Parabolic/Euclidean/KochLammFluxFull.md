# KochLammFluxFull

## Intended facts under focused verification

- the existing half-open space-time shell partition supports the directional
  terminal flux integrand;
- shell integrals of its norm are summable against
  `klFluxWeight dim`;
- the full terminal flux integrand is Bochner integrable, its shell integrals
  sum to `klFluxFull1`, and its norm is bounded by
  `klFluxSeries dim * norm w * klFluxTailC * A_p`;
- `klFluxFull_canon` chooses the shell covers directly from
  `QuantCover.exists_shell_cover`, so consumers need not package a cover.

The next value-level file combines `klFluxFull1 (sqrt t)` with `heatEarly1 t`
at every positive observation time.  The exact theorem
`ricci_flow_forward_unique` remains **0%**.
