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

## 2026-05-17 Formula 5.10 assembly aliases

Added BK-facing aliases for the new RicciFlower integral assembly handles:

- `lbl453_weighted_green`
- `lbl453_weighted_divergence_zero`
- `lbl453_shifted_trace_green`
- `lbl453_f_formula510_assembly`

These expose the proved scalar assembly route: arbitrary-test weighted Green,
closed weighted-divergence cancellation from an actual divergence field,
shifted-trace Green, and the final `formula510_of_ints` theorem.

Verification passed for this file and the targeted BK Section 6.1 module.  The
broader `BK.MSM135.Chapter06` aggregate build failed in an existing tensor
regularity import cycle, not in this wrapper.

## 2026-05-17 Formula 5.10 divergence field

RicciFlower now has the checked divergence-field construction used by the
formula 5.10 assembly:

- `connTraceVec`
- `connTraceDivEq`
- `weightedDivZero_of_connTrace`
- `formula510_of_connTrace`

No new BK alias was added in this pass; the public Section 6.1 wrappers remain
stable and continue to expose the existing formula 5.10 assembly handles.  The
remaining mathematical bridge is to construct the global smooth trace vector
`traceVec = g^{ij} A^p_ij` from the connection-variation tensor `A`.

Verification passed for the targeted BK Section 6.1 module.

## 2026-05-17 Formula 5.10 trace-field alias

Added the BK-facing alias:

- `lbl453_f_formula510_trace_field`

This exposes the RicciFlower specialization where the divergence-field input is
the constructed smooth metric trace field `tr_g A`.  BK remains wrapper-only;
the remaining proof bridge is the coordinate/component realization of the
divergence and action of this field.

Verification passed for this file.

## 2026-05-16 Formula 5.10 F-functional aliases

Switched the Section 6.1 import to the RicciFlower `F` module and added
book-facing aliases for Chapter 5 formula 5.10 as it is used by Lemma 6.1:

- `lbl453_f_functional`
- `lbl453_exp_density_variation_producer`
- `lbl453_exp_weighted_measure_variation_producer`
- `lbl453_f_first_variation_producer_of_volumeVariation`
- `lbl453_f_formula510_statement`
- `lbl453_f_formula510_final`

These expose the concrete `F` functional, the tau-free `e^{-f}dmu` variation
producer, and the final formula 5.10 statement layer.  The geometric producer
for arbitrary metric variation of `Ric + Hess f` remains in RicciFlower.

Verification: passed for this file and the targeted BK Section 6.1 module.

## 2026-05-20 Canonical formula 5.10 variation endpoint

Switched the Section 6.1 import to the RicciFlower `FirstVariation` module and
added the BK-facing alias:

- `lbl453_f_formula510_canonical_variation`

This exposes the path-based `delta_(v,h)F(g,f)` formulation.  The older
component aliases remain available as proof-layer handles, but they are no
longer the book-facing definition of first variation.

Verification passed for this file and for the targeted BK Section 6.1 module.
