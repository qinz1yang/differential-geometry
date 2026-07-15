# ParametricScalarSmulJet

## Route

The scalar multiplier is represented by the rank-zero mixed coefficient
obtained by scaling the canonical rank-zero identity. Its `appCc` action is
proved equal to `scalarSmul` after full application. This lets
`smul_jet_unif` reuse `param_app_jet`, avoiding a second iterated Leibniz
calculus.

The spacetime smoothness proof cannot use ordinary `smul_section`: the family
covers `Prod.fst : M × ℝ → M`, not the identity map.  The private
`joint_rs_smul` helper instead opens the total-space smoothness criterion and
performs scalar multiplication only in a local trivialization.  This is the
same established normal form used by existing joint tensor-family producers.

## Frontier

The source theorem is stated and proved without solution-specific assumptions.
The missing namespace opening for `iteratedCovGrad` was repaired, and the
private helpers now explicitly omit unused ambient instances.  The global
heartbeat overrides were unnecessary and have been removed.  Focused
verification passes without warnings.

`smul_jet_unif`: theorem and its dedicated scalar-multiplier machinery are
100% verified.  This is one producer in the larger A1/Galerkin chain; it does
not by itself prove the conjugate-heat or noncollapsing endpoints.
