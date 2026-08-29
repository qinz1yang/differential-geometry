# Branchwise index nonnegativity

## Status

`lIndex_sum_nonneg` is proved. For a regularized L-curve that globally
minimizes the fixed-endpoint action, it shows that the sum of the two diagonal
regularized L-index forms on adjacent branches is nonnegative when the two
smooth branch fields agree at the moving node and vanish at the outer
endpoints.

## Proof route

`exists_var_pair` realizes the two fields by globally smooth variations whose
node paths agree for every variation parameter. For each parameter,
`exists_chartH1_join` and `lAction_c1_dense` join the two slices and transfer
global fixed-endpoint minimality to the sum of the two branch actions. Hence
that summed action has a local minimum at zero.

The private `nodeAction_second` theorem differentiates the genuine moving-node
first-variation formula. `nodePair_deriv` differentiates the two endpoint
pairings using `inner_deriv_at` and covariant-derivative commutation. Their
common-node acceleration terms cancel because both branches have exactly the
same node path. The public `lRegEulerInt_deriv` producer differentiates the
Euler-residual integrals, and `indexGreen_var` converts each residual to the
index form using `lRegIndex_green`. Its integrability inputs come from
`lRegIndex_int` and `lRegJacobi_contOn`, rather than caller-supplied regularity
assumptions. Ordinary second-derivative nonnegativity at a local minimum then
gives the sign, and `lRegIndex_congr` transfers the generated variation fields
back to the original fields.

`RegAction.lean` only needed to expose the already proved genuine producers
`lRegEulerInt_deriv` and `lRegJacobi_contOn`; their proof bodies were unchanged.
No frontier wrapper, new class, stronger consumer assumption, `sorry`, or
`admit` was introduced.

## Verification and progress

Focused verification passes without warnings, and the targeted `IndexNode`
module refresh passes. `indexGreen_var`, `nodeAction_second`, and
`lIndex_sum_nonneg` now retain only the canonical `SigmaCompactSpace`
hypothesis and no longer inherit `CompactSpace`; their proofs have no compact
direct-method input. `lIndex_sum_nonneg` and its dedicated moving-node
second-variation brick are complete (100%). They are supporting machinery for
the endpoint nonsingularity argument, not the endpoint theorem itself:
`exists_lTail_inj` remains unverified (0%) at its separate action-minimality
frontier. `redVolume_anti` is complete (100%). Reusable generic infrastructure
is complete (100%); the broader dedicated L-geometry percentage is tracked in
the authoritative L-geometry plan.
