# Second derivatives along a kernel field

Owner: Chapter25 task01a07c8d-49fa-7373-9948-022395d0119a.
Claim: 3d3d42e1-1a33-4361-995d-7ed594173fe3, released after verification/registration.
2026-09-08: VERIFIED after the noncollapse checkpoint 4a461dd3f.

Target: the actual twice-differentiated local identity A(t)v(t)=0 for a symmetric
operator field, giving <A''v,v> = 2<A v',v'>. This is the one-direction algebra
in eq:scn-cone-Laplacian-kernel. The geometric cone, parallel trivialization,
trace and terminal curvature-evolution arguments remain separate Chapter25
obligations; this lemma must not be reported as full cone-terminal exclusion.
Use actual derivatives and an eventually zero kernel field, not assumed
second-derivative identities. No upstream Chapter23/24 integration.

Three public producers in DifferentialGeometry.PDE.RicciFlow.Perelman:
`inner_second_deriv_of_eventually_kernel`,
`inner_sum_second_deriv_of_eventually_kernel`, and
`inner_sum_second_deriv_pos_of_eventually_kernel`.
The finite-direction statements retain the same operator/vector base values.
Strict positivity requires a nonnegative operator and one strictly positive
variation direction; that direction still must be produced by cone geometry.

Final focused14.4s EMPTY; named lint-clean build12s; fresh external audit13.0s,
all three public declarations standard axioms only. Evidence and hashes:
`E:/lean-tools/chapter25-audit-20260908/kernel-completion.json`.
One unique root import. This is not the full cone-terminal exclusion theorem.

API findings: import `Mathlib.Analysis.Calculus.Deriv.Add` explicitly for
`HasDerivAt.add`; otherwise dot notation can select the filter-level Frechet
lemma, giving a product-filter eventual-equality goal. Use typed derivative
intermediates. `HasDerivAt.inner` takes the scalar field explicitly. The current
zero-pairing names are `inner_zero_left` / `inner_zero_right`. For a raw
eventually-equality predicate, reverse equalities pointwise with `mono` rather
than assuming `.symm` will elaborate as `EventuallyEq.symm`.
