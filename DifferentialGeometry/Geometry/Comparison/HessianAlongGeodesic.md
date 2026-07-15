# HessianAlongGeodesic

## 2026-07-14 checked result

`deriv2_comp_geo` identifies the second derivative of a smooth scalar along a
smooth geodesic with its Riemannian Hessian on the geodesic velocity.
`deriv2_comp_geo_on` is the local-germ form used by cut-locus-free squared
distance functions, and `strictConvex_geo` converts a positive Hessian on the
interior of a real convex domain into `StrictConvexOn`.

The proof uses the gradient first-derivative formula, metric compatibility,
the covariant chain rule, vanishing geodesic acceleration, and the existing
Hessian/gradient bridge. The local theorem uses `exists_smooth_germ`; no
global extension hypothesis is exposed to consumers. Focused verification
and exact target refresh passed without a local warning or `sorry`.

This comparison-layer API is complete for current B/C use. It is
infrastructure, not a compactness endpoint.
