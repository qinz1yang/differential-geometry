# LocalAddition

## Scope

This file supplies the component-local exponential addition needed by the
harmonic-map/DeTurck gauge lane.  The ambient Ricci-flow theorem does not assume
`ConnectedSpace M`, so the producer restricts the fixed background metric to
the open connected component of a chosen point and reuses the already proved
intrinsic diagonal-exponential chain there.

The canonical placement is `Geometry/Exponential/`, beside `diagExp` and its
derivative, rather than a new `Geometry/Connection/ExpMap/` directory.

## Facts written

- `connCompOpen`: a connected component as an open subtype.
- `connCompConnected` / `connCompCompact`: explicit structure producers for
  local `letI` use by downstream componentwise consumers; neither is a global
  instance.
- `connCompMetric`: restriction of the supplied smooth metric.
- `connDiagExp`: the intrinsic diagonal exponential on that component, with all
  Riemannian-distance instances kept local.
- `connAdd_zero`: zero-section value `(p,p)`.
- `connAdd_cd`: finite-order `ContMDiffAt` at the zero section.
- `connAdd_fderiv`: the chart derivative is the existing unipotent continuous
  linear equivalence.

No ambient connectedness instance, new class, new global instance, axiom, or
placeholder is introduced.

`connCompOpen` also does not expose `LocallyConnectedSpace M` as an additional
assumption.  It constructs the model and manifold locally-connected structures
inside its body from `I.toHomeomorph` and the charted-space API.

## API audit

Three mathematically different routes were checked.

1. **Current intrinsic diagonal exponential.**  `diagExp_contMDiffAt_zero` and
   `diagExp_hasFDerivAt_zero_unipotent` already prove exactly the geometric and
   analytic facts, but their intrinsic-geodesic chain is stated with
   `ConnectedSpace M`.  Restriction to the open-and-closed component is the
   shortest faithful reuse and is the route implemented here.

2. **Current chart-fixed `expMap`.**  The fixed-base theorems
   `expMap_contMDiffAt_zero` and `mfderiv_expMap_at_zero` control only the fibre
   variable.  The definition chooses `chartAt q` separately at every moving
   basepoint `q`; the selected chart domains have no coherent uniform
   neighbourhood in `q`.  Consequently those two theorems do not imply joint
   total-space smoothness, and a theorem asserting it for this chart-fixed
   object would not be a faithful local-addition API.

3. **Fresh fixed-chart flow addition.**  The joint chart-flow producer can
   define an alternative local addition without connectedness.  It would need a
   new zero-section variational derivative theorem for that chosen flow and
   would not literally be the repository's intrinsic `diagExp`.  It is longer
   and would duplicate the already proved unipotent derivative layer.

If component-local consumption proves awkward, the smallest missing transport
lemma is an open-subtype naturality statement identifying the ambient tangent
inclusion of `connDiagExp` with the ambient intrinsic exponential near the zero
section.  HMF uniqueness can instead be run componentwise and needs no such
transport.

## Componentwise HMF lift

The intended consumer does not lift `connAdd_cd` itself to a globally connected
ambient manifold.  For an arbitrary `x : M`, set `U := connCompOpen x` and:

1. restrict both Ricci flows to `U`; the existing
   `solutionOn_restrictOpen` / `isSolutionOn_restrictOpen` API supplies the
   component Ricci-flow solutions;
2. build the harmonic-map/DeTurck gauge on `U`, using `connAdd_cd` and
   `connAdd_fderiv` at points of this connected compact manifold;
3. apply connected-component forward uniqueness on `U`;
4. evaluate the resulting restricted-metric equality at `connCompPt x` and
   rewrite with `SmoothRiemannianMetric.restrictOpen_inner`.

Since `x` was arbitrary, metric extensionality gives equality on all of `M`.
Thus no global `ConnectedSpace M` instance and no ambient exponential transport
are required; the only later assembly lemma is this pointwise componentwise
extensionality wrapper.

## Verification

Focused checking is green with no warning in this file.  The named targeted
export build is also green at **3785/3785**.  The implementation reuses the
canonical `FiberBundle.t2Space_totalSpace` producer from `FiberBundleT2`; the
Riemannian bundle, continuous bundle, pseudo-emetric, and
`IsRiemannianManifold` witnesses remain local reducible definitions, so no new
global instance or class was introduced.

The component-local-addition machinery is therefore **100% source-written and
100% Lean-verified**.  Endpoint theorem `ricci_flow_forward_unique` remains
**0%**: this file supplies only the local-addition geometry needed by the gauge
construction.
