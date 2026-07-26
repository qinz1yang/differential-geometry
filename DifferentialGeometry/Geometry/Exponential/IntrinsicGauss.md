# IntrinsicGauss

## 2026-07-23 complete intrinsic Gauss pairing

The new canonical theorem `intrinsic_gauss` proves Gauss's lemma for the
time-one complete intrinsic exponential:

```text
g_exp(u)(terminalVelocity(u), d(exp)_u(w)) = g_p(u,w).
```

The proof uses the global affine launch variation
`F(s,t) = intrinsicGeodesic p (u + s • w) t`.  Constant geodesic speed and the
moving-foot speed derivative identify the transverse derivative of the
longitudinal velocity; mixed covariant derivatives commute; metric
compatibility then makes the terminal pairing affine in time.  The endpoint
variation is identified with the exponential differential by
`intrinsic_jacobi_one`.

The statement has no `ConnectedSpace`, chart source, raw exponential-domain,
or radius hypothesis.  It is therefore the lower intrinsic producer required
by the fixed-first selected inverse branch, not a wrapper around the
chart-fixed Gauss theorem.

The completed proof and its local linter cleanup passed focused verification
with no diagnostics.  Its exact artifact is current, and the file contains no
placeholders.

`intrinsic_gauss` itself is complete (100%).  The downstream fixed-first Layer
A now consumes it and is also complete (100%).  These are producer results;
the radial-Laplacian endpoint and unconditional `compactnessSol` theorem remain
separately accounted.
