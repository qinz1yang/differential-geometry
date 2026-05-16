# Section01.lean Notes

MSM135 Chapter 6.1 wrappers for `W` entropy, first variation, gradient-flow
equations, monotonicity, epsilon entropy, and lower bounds.  All wrappers defer
to RicciFlower Perelman predicates.

Verification: passed through the targeted `BK.MSM135.Chapter06` build.

## 2026-05-16 Concrete W functional wrappers

Added BK-facing wrappers for the concrete W functional and the two elementary
properties near `notes_and_commentary:lbl548`:

- `lbl544_w_functional_eq_integral`
- `lbl548_w_entropy_scale_invariance`
- `w_entropy_diffeomorphism_invariance`

The scale and diffeomorphism wrappers are proved by delegating to RicciFlower's
measure-theoretic bridge theorems.  They still require metric-layer producers
for scaling of Riemannian measure, scalar curvature, gradient-square, and
pullback change of variables.

Verification: passed for this file and the targeted BK Section 6.1 module after
refreshing the RicciFlower dependency.

## 2026-05-16 Lemma 6.1 first variation wrapper

Added BK-facing wrappers for labels `notes_and_commentary:lbl549`-`lbl552`:

- `lbl549_weighted_measure_variation_factor`
- `lbl550_weighted_measure_preserving_variation`
- `lbl551_entropy_first_variation_lemma61_of_preIBP`

The Lemma 6.1 wrapper delegates to the RicciFlower theorem proving the algebraic
final step from the combined pre-IBP formula and weighted integration by parts.
The geometric producer lemmas for the individual variation formulas remain
future work.

Verification: passed for this file.

## 2026-05-16 Actual first variation wrapper

Added `lbl551_entropy_first_variation_actual_derivative_of_preIBP`, the
book-facing wrapper where the left side is the actual derivative
`wEntropyFirstVariation` of `s ↦ W(mu_s, tau_s, R_s, G_s, f_s)`.

Verification: passed for this file and the targeted BK Section 6.1 module.

## 2026-05-16 W variation producer aliases

Switched the Section 6.1 import to the RicciFlower variation module and added
book-facing aliases for:

- `lbl549_density_variation_producer`
- `lbl551_bracket_variation_producer`
- `lbl551_entropy_first_variation_producer_of_volumeVariation`

These expose the proved scalar derivative producers and the moving-volume
producer without moving proof work into BK.  Formula 5.10 remains a later
RicciFlower-native `F` first-variation producer.

Verification: passed for this file and the targeted BK Section 6.1 module.
