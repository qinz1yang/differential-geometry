# LowRegRhsOne

## Source result

`rhs1_h2_tame` combines the concrete dimension-three affine `H2` jet bounds
for `linearizedRicciConnDiffOrder1CoeffField` and
`deTurckLieArm1Coeff` through `rhs1_h2_of_aux`.  Its hypotheses keep the
endpoint spectral `H2` radius `R` independent from the endpoint spectral
`H3` radius `A`, and its conclusion has the exact tame form
`(B0 R + B1 R * A)^2`.

The proof uses `convex_h2_jet` for the lower path jet and `convex_h3_jet` for
the full path jet.  No fourth metric derivative or high-Sobolev input enters.
The final two-arm addition is bounded by the explicit affine envelope
`4 * Ric + 2 * Lie`.

`rhs1_path_tame` applies `path_jetL2_le` to transfer this uniform
pointwise-in-path estimate unchanged to the through-second-covariant-
derivative `L2` jet of `rhsLow1PathIntegral`.  No auxiliary analytic
hypothesis, replacement producer, axiom, `sorry`, or `admit` was introduced.

## Verification and frontier

The file was written source-only while the shared sequential Lean slot was
occupied by a named artifact refresh.  It is not counted as verified until a
focused check passes.

Together with `rhs0_h1_tame`, this supplies the two affine lower-path
coefficient estimates needed by `rem_h1_of_jets` at source level.  The next
producer is the consumer-shaped smooth-core three-arm remainder/nonlinearity
estimate, followed by dense extension and the maximal-regularity solver.
`ricci_flow_unif_existence` remains theorem-level 0% until its exact statement
is proved and verified.
