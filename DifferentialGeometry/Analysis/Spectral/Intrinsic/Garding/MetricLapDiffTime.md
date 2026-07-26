# Vanishing moving scalar Laplacian operator

## State — 2026-07-10

Focused and targeted verification pass.

For a smooth realized metric family and a regular time `T`, `lapDiffA2 G T s`
is the actual operator

```text
H²(G(T)) ->L TensorL2 0 0 (G(T))
```

obtained from `Delta_(G(T-s)) - Delta_(G(T))` on the finite spectral core.

The public results are:

- `lapDiffA2_core`: eventual equality with the genuine finite-core action;
- `lapDiffA2_bound`: a support-independent modulus `omega(s) -> 0`;
- `lapDiffA2_zero`: the operator norm tends to zero.

The modulus is `sqrt C * |rho(s)|`, where `rho` is the cumulative order-one
fixed-background metric seminorm.  `metric_c1_tendsto` composed with
`s -> T-s` gives `rho(s) -> 0`.  Absolute value avoids a separate global
nonnegativity API for the supremum.

The final convergence theorem is deliberately norm-valued.  Rewriting it
through `tendsto_zero_iff_norm_tendsto_zero` caused expensive typeclass
synthesis for the full continuous-linear-map type; stating the operator-norm
limit directly is both cheaper and exactly the consumer-facing result.

## Honest progress

- Requested genuine `A2 : H²(gT) →L L²(gT)` with `omega -> 0`: complete
  (100%).
- Ready `H⁰`/strongly-measurable input for `nonaut_strong_exists`: complete
  (100%) via `lapDiffA20_short`.
- Moving conjugate-heat theorem: not proved (0%).
- Perelman no-local-collapsing theorem: not proved (0%).

## 2026-07-14 intrinsic fibre smallness

Added `lapDiff_fibreSmall`.  It fixes the perturbation size at `1 / 4` and,
near `s = 0`, produces `gFibreOpBound` for the moving-minus-frozen metric
bilinear form.  The proof composes `metric_c1_tendsto` with `s ↦ T - s`, uses
`derivNorm_le_sup`, and then applies the coefficient-one
`metricDiff_abs_le` estimate.  No extra convergence or chart hypothesis is
introduced.

Focused verification passed after the explicitly targeted upstream `.olean`
refresh.  This closes the fixed `δ < 1 / 2` input producer, not the later
time-uniform commutator/first-order Galerkin closure.

Honest accounting at the current coarse resolution is unchanged: the fixed
fibre-smallness producer is complete (100%), while `scalar_crit_tame`, the
classical moving conjugate-heat theorem, and Perelman no-local-collapsing remain
unstated/unproved (0%).  Their dedicated machinery remains about 72%, 77%, and
40%, respectively; whole HCG machinery remains about 53%, with endpoints at
0%.

## 2026-07-14 common short interval

Added `lapDiff_short`.  It intersects regular-time persistence with
`lapDiff_fibreSmall`, extracts one metric ball around zero, and chooses a
nontrivial `tau <= 1`.  Consequently every `s in [0,tau]` has both
`T-s in D.regular` and the same quarter-size `gFibreOpBound`.  This is the
common perturbative interval needed before choosing support-independent
Galerkin constants; it introduces no new consumer assumption.

Focused verification passed.  The short-interval producer is complete (100%).
`scalar_crit_tame` itself remains unstated/unproved (0%); its dedicated
machinery is now about 80%.  The classical moving conjugate-heat theorem and
Perelman no-local-collapsing remain 0%, with about 77% and 40% dedicated
machinery.  Whole HCG machinery remains about 53%, with endpoint theorems at
0%.
