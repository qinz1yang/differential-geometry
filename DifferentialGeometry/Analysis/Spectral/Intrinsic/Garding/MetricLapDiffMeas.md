# MetricLapDiffMeas

## Role

This module turns the genuine moving scalar Laplacian into the short-time
operator family required by non-autonomous maximal regularity.  It uses the
two-metric fixed-reference operator estimate to prove operator-norm
continuity, then transfers continuity through the canonical `L² ≃ H⁰`
identification.

## Intended public endpoint

`lapDiffA20_short` produces a positive time length at most one on which the
actual `H²(gT) → H⁰(gT)` perturbation is continuous, strongly measurable,
and bounded by any prescribed positive constant, both pointwise and almost
everywhere for `timeMeasure`.

## Verification status

Focused verification and the targeted module build both pass without local
diagnostics or `sorry`.  The key
performance normalization is an explicit canonical
`SeminormedAddCommGroup` instance for each large continuous-linear-map space;
this avoids typeclass search through the full reducible `H² →L H⁰` type and
does not raise heartbeat limits.

## Progress accounting

- A2 as an `H²(gT) → H⁰(gT)` operator: 100%.
- A2 measurability/uniform-smallness input: complete (100%).
- Full geometric nonautonomous input package: about 50% machinery; its final
  assembly theorem is not stated or proved (0%).
- Moving conjugate-heat theorem: 0%.
- Perelman no-local-collapsing theorem: 0%; dedicated machinery about 8%.
