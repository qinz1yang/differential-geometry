# Parametric interval integrals

## Local parameter differentiation

`hasFDerivAt_paramInt` differentiates a compact interval integral when the
integrand is jointly `C¹` on a product of open parameter and time
neighborhoods.  The derivative is the interval integral of the partial
Fréchet derivative in the parameter.  This is the local-domain counterpart
to the older global smoothness theorem in the same module.

The proof uses a compact tube around the parameter point and the integration
interval to obtain one uniform derivative bound, then applies the existing
dominated parameter-integral theorem.  It is universe-polymorphic so manifold
model spaces can use it without lowering their universe.

`paramInt_tendstoUnif` says that, for a continuous Banach-valued map on a
parameter-time neighborhood, the averages
`∫ t in 0..1, G (z, t * s)` converge uniformly on every compact parameter set
to `G (z, 0)` as `s → 0`.  The proof restricts to a compact product tube, uses
Heine--Cantor there, and applies the interval-integral norm bound.  Combined
with the weakened differentiation theorem, a jointly `C²` original map is
enough to control the parameter derivative of its removable time quotient;
no `C³` strengthening is needed.

The global `C∞` companion `contDiffOn_paramIntervalIntegral` is now likewise
universe-polymorphic.  Its proof treats the first derivative separately, then
iterates in the stable `max` universe of continuous-linear-map codomains.  This
avoids forcing a high-universe manifold model parameter into `Type 0` while
preserving the original general Banach-valued statement.

## Reuse and verification

The implementation adapts the already checked local compact-tube pattern that
had previously lived only as a private helper in the spectral tensor layer.
It now resides at the canonical calculus layer and introduces no new class or
foundational object.  Incremental diagnostics and focused verification pass
without warnings.  The local `C¹` differentiation theorem and compact-uniform
average limit have both passed focused verification; exported consumers require
one targeted module refresh.  That refresh has passed, so downstream modules
can consume both interfaces without a stale artifact.
