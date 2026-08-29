# KineticChart

## Status

Focused verification passed without warnings or placeholders.

## Checked bridges

`lKinetic_local` identifies the kinetic integral on `[a,b]` with the fixed-chart
Gram quadratic form evaluated on the weak derivative of a directly supplied
local representative `us : timeH1 E (b-a)`.  Its representative hypothesis is
already expressed in translated time:
`us.toFun r = extChartAt I p (alpha (a+r))` on `[0,b-a]`.
The forward Ricci-flow time in the coefficient is exactly
`T - (a + r)^2`.

`lKinetic_chart` preserves the earlier global-representative API as a thin
corollary: it constructs `timeH1.slice u a b` and invokes `lKinetic_local`.
Finite chart assemblies can instead construct each local representative
independently and avoid requiring one global chart-valued `timeH1` curve.

The theorem needs only:

- a `timeH1` coordinate representative whose continuous representative agrees
  with the chart coordinates on `[a,b]`;
- containment of the original manifold curve in that fixed chart on `[a,b]`;
- almost-everywhere manifold differentiability after translating the interval
  to `[0,b-a]`.

It does not require the entire curve to be `C¹`.  The proof uses the native
almost-everywhere derivative theorem for the sliced `timeH1` representative,
the fixed-chart raw-manifold-derivative bridge, and `chartGramOp_inner`.

`lKinetic_int_local` proves interval integrability of the same manifold kinetic
density directly from the local representative.  It constructs both compact
sets needed by the coefficient API:

- the image of `[0,b-a]` under `r ↦ T-(a+r)^2`;
- the image of `[0,b-a]` under the continuous representative of the sliced
  `timeH1` curve.

Metric-family smoothness then supplies continuity and a uniform operator-norm
bound for the chart Gram coefficient, and `timeQuad_int` supplies integrability
of the coordinate quadratic density.  A shared private almost-everywhere bridge
transfers this result back to the translated manifold density and then to
`[a,b]`.  Thus the theorem has no consumer-supplied measurability, operator
bound, or integrability hypothesis.

The integrability theorem assumes `I.Boundaryless`.  This is the exact geometric
condition used to turn chart-target membership of the compact coordinate image
into membership in the target interior required by `chartGramOp_cont` and
`chartGramOp_bound`; it is not needed by the bare integral identity.

`lKinetic_int` is the compatibility corollary for a global representative and
delegates to `lKinetic_int_local` after slicing.

## Boundary of the result

The weak derivative of a limiting chart-valued `timeH1` curve is not identified
with `lVelocity` of a manifold curve.  `lVelocity` appears only for the original
almost-everywhere differentiable approximant.  Lower semicontinuity for the
limit belongs to the separate varying-coefficient quadratic-form layer.

No `timeQuad` wrapper is added here: measurability and essential boundedness of
the geometric coefficient are produced by the metric-family compact-chart API,
rather than reintroduced as stronger consumer assumptions.
