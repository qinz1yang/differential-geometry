# LocalDiffeoOpen

## Role

This module restricts an ambient smooth local diffeomorphism on an open set
to a local diffeomorphism whose source is the corresponding open subtype.

## Route

`hloc_restrict_open` restricts each realizing `PartialDiffeomorph` through the
existing open-subtype `OpenPartialHomeomorph` construction.  Smoothness of the
inverse uses the existing cross-model codomain-restriction bridge.  The proof
does not introduce finite-dimensionality, derivative-invertibility, or chart
selection assumptions.

## Verification

Focused verification and the exact module refresh both passed without warnings.

The module also provides `hloc_comp`, the project-level composition theorem
for local diffeomorphisms.  It composes the realizing open partial
homeomorphisms and proves smoothness of both directions on the naturally
restricted source and target.  This closes the local API seam needed to combine
the sphere-to-universal-cover diffeomorphism with the universal-cover
projection.

## Project position

This closes the reusable open-subtype restriction seam needed by the
Killing--Hopf overlap argument.  It is infrastructure only: the global
two-chart sphere diffeomorphism and `ham3_space_box` remain separate theorem
frontiers.  This seam is complete (100%); the global two-chart theorem remains
unstated (0%), and `ham3_space_box` remains unproved (0%).  In the current
project accounting this is a small local addition to the roughly three-quarter
complete dedicated Killing--Hopf machinery, not progress on the endpoint
theorem itself.
