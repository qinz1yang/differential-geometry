# Mixed `appCcRS` H1-H2 estimate

## Verified result

`appRS_h1_h2_h1` proves the dimension-three mixed-tensor product estimate

`H1(operator field) x H2(mixed passenger) -> H1(output)`

for `appCcRS`.  Its hypotheses are the intrinsic squared jet sums through
orders one and two, respectively.  The proof uses the mixed `H1 -> L6`
embedding, finite-volume `L6 -> L3`, the sharp pointwise jet estimate for the
passenger, and the covariant Leibniz rule.

`h1_jet_sq` is the public exact bridge from the `SmoothCcTensorH1` norm square
to the zeroth- and first-covariant-derivative `L2` jet sum.  It is used to
return the mixed product estimate to the coefficient-jet shape consumed by
the low-regularity Ricci--DeTurck remainder theorem.

`appRS_h2_h2_h2` is the dimension-three mixed-tensor `H2` algebra producer.
It integrates the canonical antidiagonal Leibniz grid with the existing
two-arm Gagliardo--Nirenberg estimate.  This lets the nested VB and AMix
normal forms be assembled in `H2` before the final order-zero `H1` readout.

The focused source check and named `.olean` export passed for
`appRS_h1_h2_h1`.  The public `h1_jet_sq` bridge and `appRS_h2_h2_h2`
algebra theorem are source-complete but have not yet been rechecked because
the shared artifact repair is currently exclusive.  The edited module is
therefore not counted as fully reverified until that focused check is rerun.

## Scope

This is the abstract product producer needed by the faithful low-regularity
Ricci--DeTurck coefficient route.  It does not itself prove the concrete
`rhsLow0Coeff` or `rhsLow1Coeff` jet bounds, the mixed remainder theorem, or
uniform short-time existence.
