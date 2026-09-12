# SlabCovariantChangeBound

2026-09-10 SOURCE-WRITTEN / UNVERIFIED. Ordinary claim
a1a7f954-92e7-430e-a587-8571fb5b3cfc. Source-only during Chapter23's granted window.

Target: a constant for changing covariant derivatives which is chosen BEFORE
the two connections and the tensor field. The native ConnectionComparison
proof already uses only the numerical connection-difference bounds CA and
tensor bounds S, but its exported existential comes after the actual fields.
Moving those quantifiers is a proof obligation, not a use of choice to assert
uniformity. The new strong induction follows the native product/contraction
proof while selecting every induction constant before introducing the fields.
The native smooth component-tower API carries T2Space M; the new generic
estimate retains it. Chapter25's actual manifolds already provide this instance.

Consumer route: fix a coordinate frame, take chrR=0 and chrK to be the actual
limit metric's Christoffel coefficients. Induct on CHRISTOFFEL order a: the
lower Christoffel jets control CA through a-1. Apply the estimate to the actual
covariant Koszul tensor, a rank-three covariant combination of nabla_g(h_i-g),
whose covariant jets are directly small. Raising its last slot with h_i inverse
gives the connection difference. The already controlled lower metric jets
handle that inverse. Source Christoffel jets are jointly continuous, so their
uniform limit gives the next Christoffel jet; metric compatibility then gives
the next metric jet. Scaling the tensor makes the estimate linear in its error.

Do NOT apply this directly to the highest metric error jet and assert CA comes
from lower metric jets: an order-r metric conversion uses order-(r-1)
Christoffels, which themselves involve the order-r metric jet. That is circular.
The Koszul/Christoffel induction is needed. Nor may the native connection-change
theorem simply be swapped without proving its derivative bounds in the new
reference connection. No MetricFamilySmoothOn is assumed for the limit.

Still required: actual lower-jet Christoffel continuity, comparison evaluation
on an open neighborhood of the compact set, coordinate-jet reconstruction and
the induction proving all limit jets jointly continuous. No original proof
slot is closed by this estimate alone. Verify the saved leaf, named artifact
and all public axioms before counting it as accepted.
