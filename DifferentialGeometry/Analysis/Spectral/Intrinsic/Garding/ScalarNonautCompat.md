# ScalarNonautCompat

## Role

`lapDiffHs_eq_A20` identifies the `m = 0` member of the completed all-scale
operator with the established conjugate-heat `lapDiffA20` operator after both
are fully applied, eventually from the nonnegative-time side at the frozen
time.

The proof uses no new analytic input.  Both continuous linear maps agree on the
dense finite spectral `H²` core: `ccToHsLin_repr` realizes a finite vector by a
smooth tensor, `lapDiffHs_core` evaluates the new completion,
`lapDiffA20_core` evaluates the old completion, and `lapDiffCore_eq_cc`
identifies their common geometric action coefficientwise.

The public statement deliberately casts the input and output Sobolev exponents
after application.  Stating equality of the whole continuous-linear-map values
made elaboration normalize the reducible operator types and hit a deterministic
typeclass timeout; the fully applied scalar/vector-valued normal form avoids
that performance wall without changing consumer assumptions.

## Verification

Focused verification passes without warnings.  The exported `.olean` refresh
is separate from this source-level result.

- `lapDiffHs_eq_A20`: verified theorem completion **100%**.
- All-scale A2 time continuity: theorem **0%** and separate from this
  compatibility result.
- `galLimVel_lift`: theorem **0%**; this compatibility result is one producer,
  not the lift theorem itself.
