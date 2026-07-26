# EdgeStrongData

## Source state (2026-07-19)

`EdgeStrongData` records the exact maximal-regularity output needed from one
initial-edge Ricci--DeTurck gauge.  It contains no comparison or equality with
another solution.  Its fields are:

- `lo` in `H^1_t H^a`, with zero trace and a pointwise continuous
  representative equal to the Sobolev realization of the geometric metric
  difference;
- `hi` in `L^2_t H^(a+2)`, representing the same smooth metric difference
  almost everywhere and linked to `lo` by the canonical Sobolev inclusion;
- `force` in `L^2_t H^a`, with the fixed-background heat equation and exact
  Nemytskii identity.

`edgePath_strong` is the initial-edge reverse-realization producer.  It assumes
only closed-window continuity at the low `H^a` scale, plus the two genuine
parabolic energy outputs

```text
metric difference in L2_t H^(a+2),
time derivative in L2_t H^a.
```

Pointwise differentiability and the Ricci--DeTurck equation are required only
on `Ioo 0 T`.  Banach-space FTC on `[0,t]`, using the `L2` derivative and the
closed low-scale path, constructs the zero-trace `timeH1` representative.
Cross-scale compatibility and the heat equation are then equalities of `Lp`
classes, while `nemytskii_coeFn` gives the nonlinear identity a.e.  Thus the
remaining HMF-to-RD boundary theorem has been narrowed to an actual energy
estimate; it need not manufacture the strong-pair bookkeeping itself.

`edgeStrong_unique` consumes two such packages and the already exported mixed
forcing-ball contraction budget.  It applies `deTurckStrong_unique`, evaluates
the equal `timeH1` continuous representatives at each time, and uses
`ccToHs_injective` to recover equality of the smooth covariant tensor paths on
the whole closed window.  Thus the missing harmonic-map heat-flow producer is
not allowed to assume edge Ricci--DeTurck equality: it must construct these MR
fields separately for each gauged flow.

`edgeGronwall_zero` is a second actual edge analytic producer.  If a
nonnegative energy is continuous to zero, vanishes there, and satisfies
`E' <= K E` only on the open positive-time interval, it still vanishes on the
closed interval.  The proof applies ordinary Grönwall on `[epsilon,t]` and
sends `epsilon` to zero.  No derivative at the edge is assumed.

The source contains no `sorry`, `admit`, axiom, or opaque declaration.  It has
been statically reviewed but has not received a focused Lean check while the
coordinated workspace build is active.  Therefore `EdgeStrongData` and
`edgeStrong_unique` are source-complete but verification remains 0%.

## Three edge routes

### 1. Reverse realization from MR output

This is the faithful live route.  Once the harmonic-map heat-flow solver gives
the displayed `H^1_t H^a` and `L^2_t H^(a+2)` regularity up to time zero, the
geometric Ricci--DeTurck PDE yields `heat_eq`; the Sobolev realization gives
`scale_link`, `hi_rep`, and `path_rep`; and the initial identity gauge gives
`trace_zero`.  The nonlinear remainder identity gives `force_eq`.  No further
uniqueness theorem is missing after those fields and the existing small-time
force budget are supplied.

Exact obstruction: the current harmonic-map gauge algebra proves the interior
gauge identity, but the solver has not yet exported boundary MR regularity for
the inverse-pulled metric perturbation.  The smallest producer is therefore an
`EdgeStrongData` constructor for that gauged metric, not an equality lemma.

### 2. Difference energy with C0-small metric difference

`ricciEdgeMetric` supplies uniform C0 ellipticity.  A naive integration by
parts differentiates the inverse moving metric and appears to require an edge
bound on its spatial derivative.  There is, however, a potentially faithful
reorganization when comparing with the canonical smooth Ricci--DeTurck flow:
write the moving derivative as the derivative of the difference plus a bounded
canonical derivative.  Terms of the form
`difference * nabla(difference)^2` can then be absorbed by C0 smallness, while
the canonical pieces are lower order.  `edgeGronwall_zero` now closes the time
edge after such a structural inequality is proved.

Exact remaining obstruction on this route: the repository does not yet export
the tensor integration-by-parts identity that rewrites the full geometric
Ricci--DeTurck difference in this absorbable form.  Merely estimating the
coefficient derivative separately would be circular; the cancellation must be
proved before taking norms.  This is a distinct viable route, not ruled out by
C0 ellipticity.

### 3. Positive-time epsilon to zero

Interior Ricci--DeTurck uniqueness starts at `epsilon` only when the two metrics
agree at `epsilon`; continuity at zero gives merely that their difference tends
to zero.  Passing `epsilon` to zero would require a quantitative stability
estimate from `epsilon` to a fixed later time with constants uniform as
`epsilon` tends to zero.  The current local theorem is qualitative and its
high-Sobolev constants can blow up toward the edge.  Producing the necessary
uniform stability estimate is analytically equivalent in strength to the MR
edge package above, so this is not a shorter route.

## Endpoint accounting

The exact theorem `ricci_flow_forward_unique` remains 0% until the harmonic-map
heat-flow edge solver constructs `EdgeStrongData` for both gauged Ricci flows,
the common gauge is identified by ODE uniqueness, and the pullback is undone.
Consequently `extends_of_rmBounded` and the Hamilton positive-Ricci endpoint
still retain the Phase B dependency.  This file removes ambiguity about the
next producer but does not count as endpoint completion.

## Gauge-removal interface

For comparison against the canonical Ricci--DeTurck solution, the HMF producer
must also export the gauge's bare velocity equation on `Ico 0 T`, including the
one-sided value at zero.  The canonical DeTurck solution already has a jointly
smooth `deTurckVF` on `Icc 0 T x M`; after a Seeley time extension, the existing
`bare_forward_flow_eqOn_of_jointC1` can identify the gauges without separately
constructing an initial-time Lipschitz constant.  An HMF equation stated only
on `Ioo 0 T` is insufficient for this final ODE step.
