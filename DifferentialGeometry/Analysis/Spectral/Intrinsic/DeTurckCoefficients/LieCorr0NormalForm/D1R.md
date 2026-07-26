# D1R

## Result

The settled finite-index reduction for the first covariant-derivative correction is
now exposed as `nf_d1r`. Its generated leaf lemmas remain private to this module.

The extraction is proof-preserving: it changes only the shared definition names,
removes blank lines, and joins repeated declaration-signature lines so the module
stays below the 3000-line source limit.

## Verification

Focused verification passed without `sorry`.

## Frontier

This is an algebraic producer, not the mixed low-regularity tame endpoint. The
remaining exact normal-form chain consists of the `rz` reductions, their master
assembly, and the geometric bridge back to the Ricci-DeTurck path slope.
