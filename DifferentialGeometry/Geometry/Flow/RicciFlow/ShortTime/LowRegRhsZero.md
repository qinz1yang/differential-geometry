# LowRegRhsZero

## Source result

`rhs0_h1` assembles the complete dimension-three, pointwise-in-path intrinsic
`H1` jet bound for `rhsLow0Coeff` from existing concrete producers.  The
order-zero tail is refolded before taking norms, so the base-background
endomorphism cancels and the insertion piece uses only the perturbation `H2`
jet.  The remaining pieces are `dlbDiff_h1`, `vb_h1`, `amix_h1`, and
`riem_h1`; the Ricci and `DLa` arms are supplied by `rhs0_h1_of_aux`.

`rhs0_path_h1` applies `path_jetL2_le` to transfer that uniform coefficient
jet bound unchanged to `rhsLow0PathIntegral`.  It introduces no auxiliary
hypotheses and uses only a common endpoint spectral `H3` bound and the common
fibre ellipticity bound.

## Verification and frontier

The file was written source-only while the shared Lean slot was occupied by a
named artifact refresh.  It is not counted as verified until a focused check
passes.

This closes the unconditional order-zero coefficient/path-integral envelope
at source level.  It does not yet expose the affine
`B0 R + B1 R * A` dependence needed by the final smooth-core three-arm tame
estimate; that is a separate API refinement of the same concrete proofs,
together with a convex-path `H2` jet adapter.

The order-one half still needs a dimension-three `H2` affine-tame bound for
`deTurckLieArm1Coeff` from only the perturbation `H3` jet.  The existing
all-order producer requires a fourth metric derivative and is therefore
inadmissible for the uniform C3 theorem.  Consequently
`ricci_flow_unif_existence` remains theorem-level 0%.
