# LowRegRicciOne

## Route

`ricci1_h2_tame` is the three-dimensional low-regularity producer for the
concrete order-one Ricci connection-difference coefficient.  It separates a
lower `H2` radius `R` from the full `H3` size `A` and returns the affine bound

`B0(R) + B1(R) * A`.

The original one-parameter statement `ricci1_h2` is preserved unchanged as a
compatibility wrapper, obtained by setting `R = A` and restricting the
four-term jet bound to its first three terms.

The proof has three layers:

- the moving four-trace coefficient is controlled in `H2` by `trace2_h2`, so
  this factor depends only on `R`;
- the connection-difference kernel is reduced to the lowered connection
  difference, now using `connLow_tame` in the form
  `Bc0(R) + Bc1(R) * A`; the two slot extensions cost exactly the dimension
  factor and the five permutation arms cost a fixed factor;
- `appRS_h2_h2_h2` composes those two `H2` factors.

Quantitatively, the two exported functions are

```text
B0(R) = Capp * (2 * Bt(R)) * (15 * Bc0(R))
B1(R) = Capp * (2 * Bt(R)) * (15 * Bc1(R)).
```

No derivative above order three and no high-Sobolev ball hypothesis is used.

## Verification and accounting

The tame source and compatibility wrapper are complete but not yet counted as
verified: the parent task has not yet allocated a Lean check slot, and the new
immediate producer `connLow_tame` is itself source-only.  Once
`LowRegCoeffJets` and `H1H2AppCcRS` are refreshed, this file must receive a
focused check and named `.olean` export.  No local `sorry`, `admit`, or axiom
was introduced.

A static type audit corrected the kernel estimate to use the kernel field's
actual `(3,4)` tensor variance; the adjacent `(4,2)` variance belongs only to
the four-trace coefficient.  This correction is still awaiting the same
focused Lean check.

`ricci_flow_unif_existence` remains 0%; this theorem closes only the Ricci
half of the order-one coefficient input to `rhs1_h2_of_aux`.
