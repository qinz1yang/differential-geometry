# ParametricAppHs

## Role

`app_hs_unif` is the generic fixed-background Sobolev action estimate for a parameterized smooth coefficient tensor.  A common pointwise envelope for every covariant derivative of the coefficient gives, at each natural spectral Sobolev order, one constant uniform in the parameter and independent of the spectral support of the input.

The proof applies `app_jet_of_bdd` at each output jet order, bounds all shorter input windows by one full window, and uses `hs_le_jet` / `hsJet_le` to convert between covariant jets and the spectral Sobolev norm.

## Verified state

The file passes focused verification without `sorry`.

- `app_hs_unif`: theorem 100%; dedicated generic action-bound machinery 100%.
- `app_hs_small`: theorem 100%; dedicated sharp smallness machinery 100%.
- `appHs`: generic completed fixed-coefficient action 100%.
- `appHs_norm`: completed coefficient-jet operator bound 100%.
- `appHs_core`: smooth-core compatibility 100%.
- High-scale moving scalar Laplacian core estimate: verified theorem 100% in
  `ScalarNonautHs`; its completion layer remains separately under verification.

## Frontier

`app_hs_small` sharpens the uniform route: its right side contains the square
root of the finite squared coefficient-jet envelope.  Thus a coefficient family
whose finite jet envelope tends to zero yields operator-norm smallness after
dense-core completion; no support-dependent constant remains.

Focused verification passed without `sorry`.  The only local repairs needed
were reassociating one three-factor upper bound and normalizing a finite sum
term-by-term; the theorem statement and assumptions were unchanged.

The remaining A2 continuity frontier is geometric, not another action bound:
produce vanishing finite envelopes for `scalarTraceCoeff` and `connTraceCoeff`
from the smooth metric family (quantitatively via the existing metric seminorm
convergence/grid APIs), then apply this theorem to the Hessian and gradient
arms.  Uniform coefficient bounds alone still do not imply time continuity.

## 2026-07-15 generic completion

The file now exposes the actual completed operator
`appHs g b c n Φ : H^n(0,b) →L H^n(0,c)`.  It is constructed by extending the
linear smooth action through the dense generic spectral embedding.
`appHs_norm` lifts the finite coefficient-jet estimate to the completed
operator norm, and `appHs_core` proves the fully applied equality with `appCc`
on every smooth spectral embedding.  The core proof obtains finite
coefficient-jet bounds from compactness and feeds them to `app_hs_small`; it
never asserts equality of whole operator families.

Focused verification passed without warnings or `sorry`.  The next genuine
frontier is below completed path differentiation: a jointly smooth
rank-`(r,0)` coefficient family must first be packaged with its fixed-fibre
time derivative as another jointly smooth coefficient family.  That producer
belongs in the CovGrad parametric layer; adding differentiability assumptions
at the `appHs` consumer would merely hide this missing API.

## 2026-07-15 path support

The generic action file now also provides:

- `appHs_unif`, whose constant is chosen before the coefficient and therefore
  remains fixed along coefficient secants;
- fully applied `appHs_add`, `appHs_smul`, and `appHs_sub` identities.

Focused verification passes.  The former time-derivative frontier is now
closed by `exists_timeDerivCc` and the applied completion theorem
`exists_appHsDeriv` in `ParametricAppHsTime`.  The next frontier is the scalar
loss-two Laplacian specialization, not another generic action assumption.
