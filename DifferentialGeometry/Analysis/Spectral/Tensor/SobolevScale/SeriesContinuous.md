# `SeriesContinuous` status

## 2026-07-16 rank-generic compact mass producer

`mass_le_of_compact` is proved and focused verification passes.  It accepts a
rank-specific summable negative spectral tail and converts a continuous path
in a higher tensor Sobolev order into one summable, time-uniform lower-order
coordinate-square majorant on any compact time set.  The theorem is genuinely
rank-generic; in particular, the conjugate-heat `(0,0)` consumer does not pass
through the older `(0,2)` Weyl convenience theorem.

The proof uses the compact norm bound of the higher-order path, bounds each
weighted coordinate square by the squared Hilbert norm, and splits the lower
weight as the supplied negative tail times the higher weight.  It adds no
geometric or convergence assumption.

The theorem itself and its dedicated machinery are **100%**.  It is a small
low-level producer; it does not by itself complete scalar spacetime
reconstruction or any Perelman endpoint.
