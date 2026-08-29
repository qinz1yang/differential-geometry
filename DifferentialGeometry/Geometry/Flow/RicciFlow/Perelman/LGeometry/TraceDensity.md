# `TraceDensity.lean`

## Result

`lIndexInt_trace` is proved (100%).  At a fixed square-root time `s`, it assumes
only that the supplied finrank-sized family is orthonormal for
`S.metric (T - s^2)` at `alpha s` and satisfies the pointwise adapted equation

```text
D_s P_i = -2 s Ric#(P_i).
```

It contracts the native regularized L-index density to the exact spatial
scalar identity

```text
sum_i lRegIndexInt(P_i,P_i)
  = 2 s^2 |Ric|^2
    - (1/2) Ric(lVelocity,lVelocity)
    + s^2 Delta R.
```

No interval differentiability package, compactness assumption, regular-time
hypothesis, Hamilton `H`, time derivative of Ricci, or scalar-evolution identity
is added to the theorem.

## Contractions and signs

The adapted derivative term gives `4 s^2 |Ric|^2` before the outer factor
`1/2`, hence `+2 s^2 |Ric|^2`.  The diagonal `Rm04` trace is
`Ric(lVelocity,lVelocity)` and retains the outer negative factor `-1/2`.  The
scalar Hessian trace is the native scalar Laplacian.

For the covariant-Ricci terms, the first-slot trace is `nablaScalar(A)`, while
each divergence trace is `(1/2) nablaScalar(A)` by contracted second Bianchi.
Ricci symmetry identifies the two mixed slot orders, so the three derivative
traces cancel exactly.

The proof uses the native orthonormal basis, tensor norm, curvature trace,
scalar Laplacian realization, differentiated Ricci, Ricci symmetry, and
contracted-Bianchi APIs.  The only lower adapter needed was the reusable public
smooth-slot evaluation `nabla0S_two_apply` in the canonical Levi-Civita layer.

## Verification and project status

Focused verification passes without warnings or placeholders.  The public
theorem `lIndexInt_trace` and this L6 pointwise spatial trace-density brick are
each 100%.  The separate Hamilton-`H` / scalar-evolution assembly remains
unstated and unproved (0%), as does `redVolume_anti` (0%).

Dedicated compact ordinary-flow L-geometry machinery remains about 99%; reused
generic infrastructure for this contraction is 100%.  P2 remains below 1%, and
the whole Poincare program remains approximately 3--5%.
