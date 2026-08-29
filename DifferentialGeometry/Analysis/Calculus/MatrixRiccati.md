# MatrixRiccati

## Trace-square equality

`trace_sq_eq_iff` characterizes equality in `trace_sq_le_mul` for a symmetric
real square matrix on a nonempty finite index type: equality holds exactly when
the matrix is the scalar matrix with coefficient `trace A / card n`.

The proof separates the two nonnegative defects already present in the
trace-square estimate. Equality first forces equality in the diagonal
Cauchy--Schwarz bound and in the diagonal-to-Frobenius sum bound. A zero-variance
calculation makes all diagonal entries equal to their mean, while equality in
each row sum makes every off-diagonal square vanish. The converse is the direct
scalar-matrix calculation.

Focused verification passed without warnings. The exported declaration has not
been refreshed because no current downstream check needs the new theorem yet.
Its direct axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.
