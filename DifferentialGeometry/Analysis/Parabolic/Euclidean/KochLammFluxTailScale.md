# KochLammFluxTailScale

## Intended facts under focused verification

- the split terminal flux mass at time `R^2` extracts
  `(klLpScaleR R)^klPDual` exactly;
- taking the dual root leaves one `klLpScaleR R` and the dimension-only
  constant `klFluxTailC`;
- the selected far-tail root is bounded by `exp(-k^2/8)` times that exact
  scale factor.

The exact theorem `ricci_flow_forward_unique` remains **0%**.

## Next consumer boundary

The next producer should restrict the directional kernel to a measurable
terminal spatial piece `S`.  The pointwise comparison
`klFluxKernel_ae`, followed by `klFluxTail_fac`, gives the kernel Holder
factor

`norm w * exp (-k^2 / 8) * klFluxTailC * klLpScaleR R`.

On a piece contained in one radius-`R` ball, `KLSource1.late_lp` gives the
source factor `(klLpScaleR R)⁻¹ * A_p`; these exact scales cancel.  The
ordinary-source files `KochLammLatePiece`, `KochLammLateCover`,
`KochLammLateShell`, `KochLammLateSeries`, `KochLammLateAbs`, and
`KochLammLateFull` then provide the model for the remaining directional
finite-cover, shell, absolute-series, and full-potential identification
steps.  The resulting shell factor is the summable Gaussian
`exp (-k^2 / 8)` (with the quantitative cover-cardinality factor).
