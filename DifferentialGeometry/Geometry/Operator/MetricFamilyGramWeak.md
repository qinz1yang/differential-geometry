# MetricFamilyGramWeak

## Role

This module combines the fixed-chart Gram-operator realization with the generic
weak lower-semicontinuity theorem for time-dependent quadratic forms.

`chartKin_liminf` treats coordinate curves in `timeH1 E L`. Uniform convergence
of their continuous representatives and weak convergence of their `timeL2`
derivatives imply lower semicontinuity of the moving-metric kinetic integral.
All coordinate images are kept in one compact subset of the chart target. No
manifold-valued path class or global manifold compactness assumption is used.

`chartH1_norm_bound` supplies the coercive companion needed before weak
subsequence extraction. A common upper bound for the fixed-chart kinetic
integrals, together with one compact chart-coordinate range, gives a common
`timeH1` norm bound. Its public inputs do not expose coefficient measurability,
operator bounds, or coercivity constants.

`chartH1_subseq` composes that bound with the native `timeH1.compact_subseq`
theorem. It returns one strictly monotone subsequence, a `timeH1` limit, weak
convergence of the derivatives against every `timeL2` test vector, and uniform
convergence of the continuous coordinate representatives. Derivative weak
convergence is projected from full `timeH1` weak convergence using the test
vector `timeH1.mk 0 z`; no second compactness argument is introduced.

`chartH1_fin` is the finite moving-metric producer. It accepts a `Fin m` family
of chart centers, interval lengths, time maps, compact coordinate ranges, and
exact half-weighted kinetic bounds. It internally obtains one `timeH1` norm
bound per chart from `chartH1_norm_bound`, then applies
`timeH1.compact_subseq_fin` once to obtain a common subsequence. No norm,
coercivity, measurability, or operator-bound hypothesis is exported to the
consumer.

The coefficient passed to `timeQuad_weak_unif` is
`(1 / 2) • chartGramOp G alpha (τ r, u r)`. Thus `timeQuad_eq_integral`
produces exactly the conventional kinetic factor `1 / 2`. The theorem keeps
`τ` abstract; the Perelman regularized-time consumer can instantiate it by
`τ(s) = T - s^2`.

## Proof inputs

- `chartGramOp_cont`, `chartGramOp_unif`, and `chartGramOp_bound` supply
  coefficient measurability, uniform convergence, and an operator bound on the
  compact time-coordinate range.
- `chartGramOp_self` and `chartGramOp_nonneg` supply the self-adjoint and
  positive-semidefinite hypotheses.
- `timeQuad_weak_unif` supplies lower semicontinuity, and
  `timeQuad_eq_integral` identifies both quadratic forms with interval
  integrals.
- `chartGramOp_lower` produces the positive compact-set coercivity constant
  internally for `chartH1_norm_bound`. Compactness of the coordinate range
  bounds the initial traces; `norm_sq_eq_integral` and `timeH1.norm_sq_eq`
  then turn the kinetic estimate into the Hilbert norm estimate.
- The norm-bound proof also covers the zero-length interval, empty-set
  hypotheses, and subsingleton model space without additional consumer
  assumptions: impossible empty-range inputs close vacuously, while the
  Gram lower theorem handles the subsingleton case.
- `timeH1.compact_subseq` is reused directly for the compactness projection;
  this module adds no competing Sobolev path object or extraction theorem.
- `timeH1.compact_subseq_fin` supplies the common finite-family extraction for
  `chartH1_fin`; the empty finite family remains a genuine zero-member case.

## Verification

Focused verification passed without warnings. The file contains no `sorry` or
`admit`.
