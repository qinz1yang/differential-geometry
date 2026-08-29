# IntrinsicFramedJacobi

## Local-diffeomorphism bridge

- `framedExp_not_conj` states that a point where `intrinsicFramedExp` is a
  local diffeomorphism represents a nonconjugate tangent vector under
  `normalFrame`.
- The existing derivative-composition argument was extracted into the private
  helper `frame_not_conj_aux`. It transfers injectivity from the derivative of
  the framed exponential to the derivative of `expMapIntrinsic` using the
  surjectivity of `intrFrameCLM`.
- The existing `intrFrame_not_conj` keeps its public signature and now supplies
  the helper with `intrFrame_deriv_inj`. The new theorem instead obtains the
  same derivative injectivity from
  `IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv`.
- This is a genuine producer for the radial no-conjugacy input of
  `intrPullVol_le_hyp`; it adds no metric lower bound, completeness assumption,
  or new predicate.

## Verification

- Static source and placeholder review passed.
- Focused verification is warning-free GREEN. The named module refresh is also
  GREEN (3831/3831).

## Program status

- `framedExp_not_conj` is verified infrastructure, not either of the two exact
  P1b endpoints. P1b remains zero of two exact endpoints.
- Dedicated P1b machinery remains about 92%. The whole P0–P9 infrastructure
  remains at the authoritative 15–25%.
