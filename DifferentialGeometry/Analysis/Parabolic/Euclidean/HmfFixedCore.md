# HmfFixedCore status

## Source theorem

`HmfCoreData.core_fixed` is the Banach fixed-point theorem needed by rough
harmonic-map heat flow.  It works on one closed radius-`R` ball, proves the
untruncated fixed-point equation and zero initial trace, and exposes the
single realized nonlinear Lipschitz rate rather than baking in a particular
two-arm source split.

The proof installs the canonical completeness instance for the closed-ball
subtype locally before invoking Banach's theorem; no global instance is added.

This clean core deliberately imports no stale HMF source file.

Its only analytic import beyond Banach contraction is Mathlib's basic normed
module layer; this supplies the norm and continuous-linear-map structures
without reintroducing the stale prescribed-quadratic HMF chain.

## Verification

Focused verification is GREEN with no local warning.  The first check exposed
a missing basic normed-module import plus three elementary core proof-shape
issues (an explicit data argument for zero-ball membership and two ordered-add
inequalities); the corrected source then passed its focused recheck.  This is
machinery only; the endpoint forward uniqueness theorem remains 0% until the
geometric HMF realization and gauge argument are proved.
