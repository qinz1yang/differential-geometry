# KochLammLateMass

## Proved facts

- `klBasePow_pos`: the exact normalized Gaussian power mass is strictly
  positive for every positive exponent.
- `klTermPowMass_eq`: the full terminal-slab
  `L^((n+4)/(n+2))` heat-kernel power integral is evaluated exactly by
  Fubini as the terminal time factor times `basePowMass`.

The proof uses the actual translated heat kernel and the restricted product
measure.  The terminal slice `s = t` is removed only as a null set; no false
pointwise positive-time assertion is made there.

## Remaining frontier

The exact formula must next be converted into the radius scale
`R^(4/(n+4))`, paired with `klLateSrc_norm`, and combined with the far spatial
shell sum.  The exact theorem `ricci_flow_forward_unique` remains **0%**;
Ricci--DeTurck realization and the harmonic-map gauge remain downstream.
