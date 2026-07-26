# LowRegCoreTame

## Role

This is the final smooth-coefficient assembly layer for the dimension-three
low-regularity Ricci--DeTurck estimate.  It does not use the coarse
`rhs_h1_lip` route.

## Proved source facts

- `rhs0_path_tame` transfers the affine pointwise path bound
  `B0 R + B1 R * A` for `rhsLow0Coeff` to the `H1` jet of
  `rhsLow0PathIntegral`.
- `rem_h1_tame` combines `rhs0_path_tame`, `rhs1_path_tame`, and
  `rem_h1_of_jets`.  Its top arm is
  `Ctop * R * ‖T - T'‖_H3`; its fixed lower arm depends only on `R`; and
  endpoint `H3` sizes occur only in a coefficient multiplying
  `‖T - T'‖_H2`.
- The endpoint `H2` radius `R` and endpoint `H3` size are independent.  The
  proof chooses the latter only after fixing `T,T'`, as the sum of their two
  `H3` norms.
- `smoothN_h1_tame` identifies the remainder estimate with the spectral
  difference of the genuine smooth nonlinearity.
- `coreN_tame` is the consumer-shaped specialization on `smoothCore`.  It
  uses `coreRep_spec`, the spectral inclusion identity, and contraction of
  `symmS`; its right-hand side has exactly the top-difference, fixed lower,
  and high-size-times-lower-difference arms expected by the tame extension.

## Verification

Source assembly is complete and contains no `sorry`, `admit`, axiom, new
class, instance, or notation.  Lean verification was intentionally not run
while the shared named build occupied the only Lean slot.

## Remaining bridge

The next step is no longer analytic or representational: apply
`dense_tame_extend` to `coreN_tame`, then feed the resulting continuous
lower-state nonlinearity to `partial_sol_tame` after choosing a positive
radius that satisfies both smallness arms.

## Honest status

`ricci_flow_unif_existence` is still unproved (endpoint 0%).  Its dedicated
dimension-three mixed-estimate machinery is substantially advanced, but the
unchanged public theorem is dimension-generic and also still needs the
low-regularity solver, same-horizon smoothing, and final packaging.
