# KochLammFluxNear

## Proved

- `klFluxSrc_memLp` and `klFluxSrc_norm` expose the finite and quantitative
  late-cylinder `L^(n+4)` consequences of `KLSource1.late_lp`.
- `klFluxNear_holder` pairs a directional first-derivative heat kernel with
  that source on the same late cylinder using the exact conjugate exponent
  `(n+4)/(n+3)`.

The proof stays in joint space-time and does not infer a time-slice norm.

## Frontier

The next layer bounds the kernel factor by the global radial majorant,
inserts `klFluxNorm_scale`, and cancels `klLpScaleR R` against the source
factor.  This machinery does not yet complete either endpoint theorem; both
remain `0%`.
