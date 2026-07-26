# FineGramBounds

## Producers

`bufferGram3_bnd` is the non-circular entry point.  For a fixed compact
carrier inside one chart, it first chooses a positive collar radius `r0` using
only compactness and the open chart target.  On the resulting fixed compact
pullback buffer it then obtains one family-uniform constant for all raw Gram
jets through order three.  The refinement radius can therefore be chosen
after this constant, subject to `r <= r0`.

`fineGram_of_orders` applies the public `chartGram_of_orders` theorem to each
compact pullback of a refined outer closed coordinate ball and takes a finite
nonnegative sum of the constants.  It supplies one family-uniform raw
chart-Gram bound at a fixed order.

`fineGram3_bnd` additionally aggregates the four orders `q = 0,1,2,3`, giving
one nonnegative constant valid for every refined center, every metric in the
family, every point of the corresponding outer compact set, and every Gram
component.

The two `fineGram...` theorems are convenient monotone readouts after a
refinement has already been selected; `bufferGram3_bnd` is the producer used
when the small radius itself must depend on the coefficient constant.

The `MetricCovDerivOrderBoundOn Set.univ` input is restricted directly to each
outer compact set.  The original POU weight never appears in the coefficient,
so there is no division by a weight which may vanish at the boundary of its
support.

## Remaining estimate

This file bounds the raw forward Gram jets.  The next producer must combine
these bounds with uniform inverse-Gram entry control and the inverse derivative
identity to obtain a spatial Lipschitz estimate for the inverse Gram principal
coefficient on each outer ball.  The straight segment is legitimate because
`FineChartCover` keeps the entire closed outer coordinate ball inside the chart
target.

## Verification

Source construction and static inspection are complete.  Lean verification is
deferred while the shared named build lane is occupied.  This file contains no
`sorry`, `admit`, axiom, opaque declaration, replacement hypothesis, or new
foundational class/instance/notation.

Endpoint completion remains 0%; this is family-uniform coefficient machinery.
