# HeatEarlyFluxSeries

## Verified producer

`fluxShellWeight d k` is the exact polynomial-exponential majorant needed by
the early first-derivative heat potential after a quantitative ball cover:

```text
(5(k+1))^d * (k+1) * exp(-k/4).
```

The extra `(k+1)` is the scaled-radius factor in the first spatial derivative
of the heat kernel. `fluxShellWeight_sum` proves summability by reducing to
Mathlib's canonical polynomial-times-exponential series at degree `d+1`.
`fluxShellSeries` packages its ENNReal mass, and
`fluxShellSeries_ne_top` proves that mass is finite.

The focused Lean check passes with no warnings. The source contains no
`sorry`, `admit`, axiom, opaque replacement, new class, instance, or notation.

## Honest frontier

This file proves the global shell-series convergence but does not itself pair
a shell with a source. The next producer combines it with
`heatEarly1Near_norm`, `exists_shell_cover`, and `heatD1Maj_early` to prove the
full early divergence-potential value bound. The exact
`ricci_flow_forward_unique` and `ricci_flow_unif_existence` theorems both
remain 0%.
