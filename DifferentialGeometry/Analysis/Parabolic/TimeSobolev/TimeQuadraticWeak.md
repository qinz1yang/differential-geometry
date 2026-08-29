# Weak limits of time quadratic forms

## Result

`timeQuad_weak_lim` proves lower semicontinuity for quadratic energies whose
operator coefficients converge uniformly in essential operator norm while the
inputs converge weakly in time `L²`. Each approximating coefficient may use its
own essential bound; no uniform bound parameter is required.

`timeQuad_weak_unif` is the corresponding rate-free interface. It accepts the
filter-shaped statement that every positive real tolerance eventually bounds
the coefficient error almost everywhere. This is the direct consumer of
geometric `TendstoUniformly` results and avoids introducing an artificial
`NNReal` error sequence in the geometric layer.

Only the approximating operators are assumed self-adjoint and positive
semidefinite. The limiting operator needs no duplicate positivity or symmetry
hypothesis.

## Proof route

The proofs use square completion. Two applications of the matching time-operator
weak convergence theorem identify the mixed term and the fixed-limit-vector
term. Positivity of each approximating quadratic form then gives the required
eventual lower bounds. Banach--Steinhaus bounds the weakly convergent input
sequence. In the rate-free theorem, the unit coefficient tolerance gives an
eventual operator bound, which is exactly enough for the coboundedness required
by the real-valued `liminf` API; no uniform bound on every initial coefficient is
added.

## Verification

Focused verification passes without warnings or placeholders.
