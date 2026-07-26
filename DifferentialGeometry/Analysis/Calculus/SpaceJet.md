# SpaceJet

## Role

`SpaceJet.lean` is the canonical calculus-level home for transporting joint
regularity of a parameterized normed-space-valued function to joint continuity of its
spatial iterated Fréchet derivatives.  It keeps this general affine-slice
argument below the Ricci-flow and HCG compactness layers.

## Current verified interface

- `spaceJet_contOn` handles every spatial order `k` allowed by a finite or
  infinite joint regularity order `n`, on an arbitrary open subset of `ℝ × E`.
- `spaceJet_contAt` extracts the finite-order neighborhood available from a
  pointwise `ContDiffAt` hypothesis and gives the corresponding pointwise
  joint continuity statement.
- `SpaceJetDiff q G J V` is the anisotropic bootstrap invariant: every spatial
  iterated Fréchet derivative of `G` is jointly `C^q` on `J × V`.
- `spaceJet_comp` proves that this invariant is preserved by a smooth
  postcomposition on an open target set.  The proof uses Mathlib's finite
  Faà-di-Bruno formula (`iteratedFDeriv_comp` and
  `FormalMultilinearSeries.taylorComp`) and does not add a regularity or image
  assumption beyond the natural maps-to premise.
- `SpaceJetDiff.fderiv` and `SpaceJetDiff.prodMk` are the two generic closure
  operations used to assemble finite spatial jets.  `SpaceJetDiff.jet2`
  packages the value, first derivative, and second derivative with the same
  joint finite-order regularity, while `SpaceJetDiff.jet_fderiv` exposes the
  spatial derivative of an arbitrary order-`r` jet for the PDE bootstrap.
- The proof reuses the checked affine-translation and spatial-inclusion route:
  restrict the full joint jet through `ContinuousLinearMap.inr`, then use the
  continuous-linear restriction map on multilinear maps.
- `Analysis.jet2_sub_le` packages common bounds for orders zero, one, and two
  into a norm bound for the full `jet2` product.
- `Analysis.jet2_contOn` reconstructs continuity of the full `jet2` family
  from continuity of those three iterated Fréchet-derivative families.  This
  is the generic limit-jet continuity input needed before compact-image
  composition with the chart Ricci operator.

Verification status: focused check passed.  The standalone calculus module
needs both the composition and operation rules for `ContDiff`; with those
minimal Mathlib imports, the affine-slice, finite Faà-di-Bruno, derivative,
product, and two-jet closure proofs are green.  The derivative closures use an
explicit bounded-linear curry map so that the canonical normed instances on
finite-arity continuous multilinear maps are preserved.

## Project accounting

The public generic spatial-jet calculus requested by the P4 route is complete
(100%).  It is supporting machinery only: `ConvOut.gramSmooth` remains an
unproved theorem (0%), the broader P4 regularity machinery remains about 90%,
and the whole HCG compactness project remains about 60% by the current
project-map denominator.
