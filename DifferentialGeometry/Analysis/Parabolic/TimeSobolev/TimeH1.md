# Time H1 paths

## Implemented API

`timeH1.ofContDiffOn` realizes a vector-valued `C¹` curve on `Icc 0 T` as the
continuous representative of a `timeH1` element for the weakest natural time
assumption `0 <= T`. It uses the ordinary derivative as the L2 representative;
the one-sided endpoint issue is removed almost everywhere rather than by
asserting differentiability outside the interval.

`timeH1.toFun_ofContDiffOn` proves equality with the original curve on the
whole closed interval, including the degenerate case `T = 0`.
`timeH1.deriv_ofContDiffOn` identifies the weak time derivative almost
everywhere with the ordinary derivative.

`timeH1.chain_ae` is the generic weak chain-rule uniqueness theorem needed by
chart overlaps. Given two existing `timeH1` curves whose continuous
representatives agree through a map on `Icc 0 T`, a supplied relative Frechet
derivative of that map along the first representative relates their weak
derivatives almost everywhere. The derivative is allowed to be within an
arbitrary set, so the theorem applies to model-with-corners coordinate changes
without an ambient openness or boundaryless assumption.

## Verification and boundary

Focused verification passes without warnings or placeholders. This API is
generic finite- or infinite-dimensional linear infrastructure. `chain_ae`
does not construct a nonlinear composite in `timeH1`; it proves the derivative
relation once both `timeH1` representatives and their pointwise composition
identity are available. This is the weaker fact actually needed to identify
separately extracted chart limits.

For the Perelman direct method, weak chart compatibility is now discharged by
`chartH1_overlap`. The next generic analytic producer is stability of `timeOp`
under a uniformly convergent bounded coefficient and a weakly convergent
`timeL2` input. Finite chart localization, moving-coefficient lower
semicontinuity, and a separate Tonelli regularity upgrade still remain.
`exists_lMinimizer` remains 0%.
