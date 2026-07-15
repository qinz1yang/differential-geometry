# MetricKoszul

## Role

This module is the realization bridge between the model-space metric-jet
algebra in `Metric/TensorInner/MetricKoszul.lean` and the canonical
Levi--Civita connection.  It must remain connection-facing: it does not define
a second primitive Christoffel symbol.

## Current state

- `const_flat_eq_koszul` identifies the lowered Levi--Civita derivative of
  constant model-space vector fields with the coordinate Koszul covector.
- `const_cov_eq_koszul` raises the equality through an explicit coercive
  metric.
- `const_flat_eq_nhds` and `const_cov_eq_nhds` replace global coefficient
  equality by equality on a neighborhood of the evaluation point. This is the
  locality API needed after bump-extending a metric from an open ball.
- `cov_eq_fderiv_add` is the moving-field realization: the model-space
  Levi--Civita derivative is the Frechet derivative plus the raised Koszul
  correction.  It is a thin projection of the existing chart-Christoffel API,
  not a second connection or Christoffel hierarchy.

The initial elaboration attempts exposed only explicit tangent-bundle model
inference and the existing nonzero-finrank requirement.  After stating those
canonically, focused verification and the targeted build passed without local
proof or style warnings.

## Frontier

`normal_cov_eq_fderiv` now consumes the moving-field theorem for the total
bump extension of the normal-ball metric.  The remaining geometric bridge is
the local-germ/cross-model pullback identification for the selected inverse
field through the normal-ball diffeomorphism.  Any missing reusable API should
be metric/connection germ locality, not another Koszul hierarchy.
