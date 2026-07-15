# PhaseEndpointInverse

## Current state

- `freeDiagInv_pos` proves positivity of the reciprocal inverse norm of the free
  retained-endpoint equivalence on a nontrivial phase space.
- `exists_quant_inv_bi` is the stronger canonical producer.  It turns an
  `ApproximatesLinearOn` estimate on a positive closed ball into an
  `OpenPartialHomeomorph` with exactly that open-ball source, an explicit
  positive closed ball in its target, and the quantitative
  `ApproximatesLinearOn.to_inv` witness for the exact constructed inverse.
- `exists_quant_inv` is a compatibility projection of the stronger theorem, so
  existing consumers keep the same statement.
- `inv_smooth_of_approx` proves the reusable same-branch regularity theorem for
  any supplied `OpenPartialHomeomorph` whose source and forward function agree
  with the quantitative construction. `quantInv_smooth` remains the wrapper
  for `ApproximatesLinearOn.toOpenPartialHomeomorph`. The proof consumes the
  canonical calculus theorem `ApproximatesLinearOn.fderiv_sub_le`, obtains
  derivative injectivity from the strict inverse threshold, upgrades it to
  bijectivity in finite dimension, and applies
  `OpenPartialHomeomorph.contDiffAt_symm`.
- Focused verification passed without local warnings or placeholders after
  both the calculus migration and the stronger inverse producer.

## Scope

This is a generic analysis-layer inverse theorem.  It contains no geometric
endpoint identification and does not prove the HCG moving inverse by itself.
The next shared-producer frontier is to preserve the retained inverse estimate
through the selected normal branch at theorem level, without adding a field to
`IsNormalDiag`, and then derive the velocity-slice derivative estimate.  The
scaled radius selector will also need an explicit small inverse-error budget;
mere invertibility does not make that error arbitrarily small.

## HCG accounting

The generic inverse materialization is complete, but `CmHessianInput` and
`StrictDistInput` remain separate unproved endpoint producers.  This change is
supporting machinery only and does not advance either theorem above zero.
# Quantitative phase-endpoint inverse

## 2026-07-14 retained inverse estimate

`exists_quant_inv_bi` preserves the inverse approximation supplied by the
quantitative inverse theorem, while the legacy `exists_quant_inv` remains its
statement-compatible projection.  The generic `invVel_approx` and
`invVel_fderiv_le` read the second component on a fixed-endpoint slice and
bound its derivative relative to `-id`.  These are producer-side estimates;
`invErr_lt_one` supplies a reusable sufficient smallness threshold for that
error to be strictly below one.  The HCG scale selector must still instantiate
and retain this witness before Neumann invertibility can be claimed.
