# Pullback Defs notes

## 2026-06-05 source-check repair

A direct source check of `Pullback/Defs.lean` failed at
`bilinear_pullback_bundle_smooth`: the original `flipₗᵢ.contDiff` route used the
continuous-linear-map seminormed instance, while the `ContDiff` proof expected
the normed-space instance.

The repair imports the normed operator-space instances and proves smoothness of
`ContinuousLinearMap.flip` through a local `LinearIsometryEquiv` built with the
normed-derived seminormed instance.  The nearby unused-section-variable warnings
were cleaned with local `omit`s.

Verification passed for `Pullback/Defs.lean`.
