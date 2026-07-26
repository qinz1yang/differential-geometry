# ConvFieldOpenEndgame

## 2026-07-17: open-window endgame assembly

Goal: close the P4 open-interval consumer without asking for convergence at
the two endpoints of the ambient interval.

Implemented source:

- `OpenConvOut.isSolution`: combines the global open chart-Gram regularity,
  metric-family smoothness, open-window Ricci equation, and the canonical
  scalar/Ricci/Rm continuity producers into `IsSolutionOn`.
- `flowUpgrade_of_open`: copies the checked `flowUpgrade_of_maps` data
  assembly, but answers each requested compact `Icc` by placing it inside one
  canonical closed window and applying `ofRP_supOn_conv` there.
- `flowLimit_of_open`: the direct conclusion consumer.
- The canonical `OpenConvOut.scalar_conv` is reused from
  `ConvFieldOpenScalar`; its existing canonical-window proof is not duplicated
  here, and `flowUpgrade_of_open` keeps the stable scalar-convergence input
  rather than repeating the large raw-bound hypothesis block.

No endpoint convergence hypothesis, radius assumption, or new field is added.
The source theorem names stay within the project naming limit.

Verification passed.  The first focused pass exposed an over-strong
`CompactSpace` parameter on the four `ExtendedSolutionRegularity`
chart-Gram-to-curvature producers.  That section-variable leak was removed in
the canonical lower modules and `ExtendedSolutionRegularity`; no compactness
assumption or duplicate coordinate proof was added here.  After the canonical
refresh, the full noncompact `ConvFieldOpenEndgame.lean` passed its focused
check with no diagnostics.

Accounting (kept separate):

- `OpenConvOut.isSolution` theorem: 100%; its dedicated assembly machinery is
  100%.
- open-window endgame theorem family: 100%; its dedicated wiring is 100%.
- P4 dedicated machinery: approximately 94%; the unconditional P4/HCG
  endpoint remains 0% until all raw-window and completeness producers are
  assembled.

## 2026-07-18: retained-flow projection

Added `flowUpgrade_open_L`, the canonical projection theorem stating that
`flowUpgrade_of_open` retains its supplied `PointedFlowData` as `data.L`.
This exposes an existing record field without unfolding the full endgame
definition downstream and adds no assumption or parallel API.

The first proof attempt let `subst P` choose `hPlim`, which left the dependent
specialization unreduced.  Eliminating the prescribed equality `hPL` directly
fixes `P` to `L.atTime 0`, after which the projection is definitional.
Focused verification passed with no diagnostics.

## 2026-07-18 grow-local endgame propagation

All open-endgame declarations now expose the revised grow-local covariant-tail
premise. No proof or endpoint field changed. Focused verification and the
exact module refresh pass.

## 2026-07-24 retained intrinsic Ricci norm

The open-window upgrade now takes the concrete `RicNormPullback` produced by
the open convergence readout and stores it in `FlowLimitData`. The projection
and conclusion wrappers thread the same witness; they add no new mathematical
premise to the raw assembly endpoint.

Source wiring and focused verification pass with no diagnostics, and the exact
open-endgame artifact is current. The upstream Ricci-norm producer and
open-window readout artifacts are also exact-current.
