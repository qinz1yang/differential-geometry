# Compact-factor collapse with the Pythagorean product metric: MC16

`WithLp 2 (X × Y)` is Mathlib's genuine L2 product metric. The proof first
establishes for arbitrary metric factors that its distance is
sqrt(dX²+dY²), then that projection to X has distortion at most dY.
No max-product metric is substituted. Standard nonemptiness and compactness
instances are transported through Mathlib's existing WithLp equivalence and
product homeomorphism; no competing product topology is defined.

`GromovHausdorff.ghDist_prod_le_half_diam` proves
  dGH(X ×₂ Y, X) ≤ diam(Y)/2
for nonempty compact metric factors. Exact surjectivity of projection means
that the general approximate-subset bound has zero coverage errors. The
variant `ghDist_prod_le_of_diam_le` accepts any proven upper bound on the
factor diameter. `tendsto_ghDist_prod_of_tendsto_diam` allows varying compact
factors whose diameters tend to zero.

`productFstApprox` supplies actual pointed approximation maps for arbitrary
X, compact Y and diam(Y)<ε<R. At a target point x, the exact lift (x,q)
has distance dX(x,p) from (p,q), so actual ball coverage is proved.
`pointedGHConverges_product_of_tendsto_diam` gives the corresponding pointed
convergence for a complete, possibly noncompact base and arbitrary chosen
fiber basepoints.

Source: blueprint207A MC16, section metric examples; BBI8.2 scaling/product
conventions and KL Section2.2, printed19–20/PDF14–15, checked in the unchanged
revision58 record. The sqrt distance estimate is proved directly. Mathlib
WithLp/ProdLp and ghDist_le_of_approx_subsets were inspected on the pinned
commit. At this stage the literal fixed-factor t-scaled metric and its diameter
transport remain a separate scalar-metric adapter; no flat-torus manifold
or Riemannian normalization witness is asserted by these generic results.
