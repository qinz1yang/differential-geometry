# Hessian trace realization

## 2026-07-10: connection-difference producer

`hess_sub_conn` is now checked.  For two smooth tangent-bundle covariant
derivatives, it identifies the pointwise difference of the canonical scalar
Hessians with minus `connectionDifferenceOutput` of
`CovariantDerivative.difference` contracted against the canonical `duSec`.

The proof stays invariant: extend two fiber vectors to smooth global sections,
use `hessianSec_nabla` for both connections, apply `nabla0SFun_sub_cov` in rank
one, and finish with `connectionDifferenceOutput_apply`.  No coordinate
constancy hypothesis, `HasLocallyConstantChartAt`, or new consumer assumption
is used.

Focused verification passed without warnings.  This local producer is complete
(100%).  The moving-metric `A2` estimate itself is still unstated/unproved
(0%); its dedicated machinery is roughly 50%, because the metric-trace
difference and support-independent analytic bounds still need assembly.  The
Perelman no-local-collapsing endpoint remains 0% proved, with dedicated
machinery roughly 27%; the broader HCG infrastructure is roughly 45% while its
main endpoint theorems remain 0% proved.

## 2026-07-10: scalar Laplacian split

`lap_sub_conn` is now checked.  It rewrites the difference of scalar
Laplacians for two connection/metric pairs as the change of metric trace on the
reference Hessian, minus the reference metric trace of
`connectionDifferenceOutput` applied to `duSec`.

The proof reuses `scalarLap_smooth` for both Laplacians and `hess_sub_conn` for
the Hessian difference.  The only remaining step is linearity of `inner0S` in
the traced tensor.  It does not introduce a contravariant inverse-metric tensor,
coordinate hypotheses, `HasLocallyConstantChartAt`, or any new consumer
assumption.  Focused verification passed without warnings.

This producer is complete (100%).  The moving-metric `A2` theorem remains
unstated/unproved (0%); its dedicated machinery is now roughly 55%, with the
support-independent scalar Hessian estimate and the quantitative metric/connection
coefficient modulus still to be assembled.  The Perelman no-local-collapsing
endpoint remains 0% proved, with dedicated machinery roughly 28%; broader HCG
infrastructure remains roughly 45%, while its main endpoint theorems remain 0%.

## 2026-07-16: Hessian/covariant-gradient pairing

`hessSec_inner_cov` is now checked.  For any metric-compatible smooth
connection, it evaluates the canonical `hessianSec` on arbitrary tangent
vectors and identifies the result with the metric pairing of the covariant
derivative of `gradientFun`.  The statement is basis-free and fully applied to
a scalar; it does not assert equality of whole tensor or Hom objects.

The proof extends the two pointwise tangent vectors to smooth sections, uses
`hessianSec_nabla`, and cancels the one-form correction term with
`metric_compatible_apply`.  It adds no supplied component, Bianchi, coordinate,
or chart-local-constancy assumption.  Focused verification passed without
warnings.

This adapter is complete (100%).  The downstream `ricDriftDiv` producer and
`weighted_hess_split` theorem are still unstated/unproved (0% each); their
dedicated geometric machinery is roughly 60%, because the Ricci--Hessian trace
contraction and canonical contracted-Bianchi assembly remain.  The Perelman
no-local-collapsing endpoint remains 0% proved, with dedicated machinery roughly
28%; broader HCG infrastructure remains roughly 45%, while its main endpoint
theorems remain 0%.
