# ActionSplice

## Goal

Realize one positive-length fixed-chart `timeH1` replacement inside a finite
monotone chart subdivision, including subdivisions with repeated nodes away
from the selected piece.

## Route

The selected coordinate curve is first composed with the continuous projection
onto its compact parameter interval.  This gives a globally continuous chart
lift without assuming anything about the chosen `timeL2` representative away
from the interval.  The global curve is then the requested closed-interval
piecewise splice.  Equal endpoint traces identify the two branches on the
frontier.

For every other segment, finite-index order gives either
`j.succ <= i.castSucc` or `i.succ <= j.castSucc`.  Monotonicity therefore makes
an overlap with the selected closed interval a single endpoint, even when other
subdivision nodes repeat.  This supplies both source membership and the
dependent `Function.update` representation identity.

## Verification

Focused verification and the targeted module refresh passed without warnings.
The source contains no placeholders.  The public theorem name is within the
project's twenty-character limit.

## Project position

- `exists_chart_splice`: 100%.
- One-piece splice machinery: 100%.
- Local chart-minimality transfer: still 0% until its theorem is stated and
  proved; this splice discharges its previously missing topological producer.
- Terminal regular minimizer theorem: 0%.
- Reduced-volume monotonicity: 0%.

The theorem does not require the flow, scalar curvature, compactness, manifold
smoothness, or a boundaryless model.  It is the topological input for
transferring the relaxed global minimum to local chart-`timeH1` minimality; it
does not itself perform the action comparison or prove regularity.
