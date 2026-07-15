# StepCPairGeometry status

Status: 2026-07-13.  `sigmaBall_nesting` passed focused verification.  The
downstream `pair_exp_maps` composition is saved and awaiting its focused check
after the concurrently invalidated upstream object chain is refreshed.

`sigmaBall_nesting` is the missing numerical producer for a stable intersecting
ordered pair: the physical `16 * lamInf alpha` source ball lies in half of the
item-3 target ball.  The factor one-half is essential for the coercivity
conversion back to target normal coordinates without strengthening the fixed-D
budget.

`pair_exp_maps` composes this nesting with `exp_sigma_maps`, the item-3 source
C2-radius fact, the H6 center coercivity bound, and the half item-3
`expRadiusGp` tail.  It is not counted complete until the focused check passes.
The numerical nesting sub-brick is 100%; the pair exponential-containment
composition is provisionally about 85%.  Dedicated Step-B/B1 machinery remains
about 83%, Chapter 4 machinery about 79%, and whole-HCG machinery about 53%.
`StepB1RawInput`, textbook B1, and the conditional compactness endpoint remain
theorem-level 0%.
