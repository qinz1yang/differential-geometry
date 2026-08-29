# JacobiRiccati

## Mean-square equality

`mean_sq_eq_iff` is the geometric equality case of `mean_sq_le_shape`. Under
the same perpendicular Jacobi-family hypotheses and positive transverse
dimension, equality holds exactly when `curveShape` is the scalar matrix whose
coefficient is `curveMean` divided by the transverse dimension.

The common orthogonal-complement construction now lives in the private helper
`shape_trace_model`. It represents the shape operator by a symmetric matrix in
an orthonormal perpendicular basis, preserves the trace and square trace, and
transfers scalar-matrix equality between that basis and the original Jacobi
basis. The public equality theorem then reuses `trace_sq_eq_iff`; no new
geometric assumption or predicate is introduced.

`mean_riccati_eq_iff` packages the next routine numerical step without adding
ODE hypotheses. Equality in the Riccati upper bound is equivalent to simultaneous
saturation of the Ricci lower bound in the velocity direction and scalarity of
the shape matrix. Smoothness and Jacobi-equation hypotheses used only for the
separate derivative identity are intentionally absent from this equality lemma.

Focused verification passed without warnings. Direct axiom audits for both new
public theorems report only `propext`, `Classical.choice`, and `Quot.sound`.
The direct upstream `MatrixRiccati` export refresh passed.
