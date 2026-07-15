# ProperBallExp status

Status: 2026-07-13, both bridge theorems passed focused verification without
warnings or `sorry`.

`properBall_to_exp` converts a closed ball for any supplied metric realizing
the stored Riemannian emetric into an exponential image.  Its only radius data
are the existing `expRadiusGp` bound and the sharp coercivity-adjusted coordinate
bound.  `exp_sigma_maps` combines the public radial upper bound from
`GaussLemma` with a factor-two center-metric comparison to send the canonical
sigma coordinate ball into the `16 * lam` physical ball.

These are generic producer-side adapters; they introduce neither a new endpoint
radius field nor a parallel proper-metric package.  The local bridge layer is
100%.  Stable-pair numerical nesting and H6/item-3 specialization remain in
`StepCPairGeometry`.  Dedicated Step-B/B1 machinery is about 83%, Chapter 4
machinery about 79%, and whole-HCG machinery about 53%; `StepB1RawInput`,
textbook B1, and the conditional compactness endpoint remain theorem-level 0%.
