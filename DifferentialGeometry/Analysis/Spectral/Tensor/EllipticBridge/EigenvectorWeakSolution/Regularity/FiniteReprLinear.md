# FiniteReprLinear

## Purpose

`finiteReprLin` packages the existing finite-support spectral representative as
a genuine real-linear map from `tensorHs.finiteSupportSubmodule` to
`SmoothCcTensor`.  It is infrastructure for later operator constructions; it
does not itself state or prove the nonautonomous `A2` estimate.

## Implementation

The map first turns the coefficient function of a subtype element into a
`Finsupp` with `Finsupp.ofSupportFinite`, then applies
`Finsupp.linearCombination` to the existing `eigenvectorSmooth` family.
`finiteReprLin_apply` identifies this construction with
`tensorHsSmoothRepr v.1 v.2` by normalizing the same finite sum.

No new geometric, regularity, or support assumptions were added, and the
existing high-cost representative module was not modified.

## Verification

Focused verification passed without warnings.  This linear packaging helper is
complete; the downstream `A2` theorem remains a separate, unstated target.
