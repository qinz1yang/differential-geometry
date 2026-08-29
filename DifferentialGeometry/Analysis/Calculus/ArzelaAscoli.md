# Compact-target Arzela-Ascoli

## Implemented surface

`arzela_subseq_cpt` extracts a strictly monotone uniformly convergent
subsequence from an equicontinuous sequence of continuous maps on a compact
source when every value lies in one supplied compact target set.

The theorem reuses Mathlib's bounded-continuous-function Arzela-Ascoli theorem,
compact sequential extraction, and the equivalence between convergence of
bounded continuous functions and uniform convergence. It does not introduce a
path-space structure or specialize the result to vector-valued maps.

## Verification

Focused verification passes without warnings. No new proof assumptions or
unfinished declarations were introduced.
