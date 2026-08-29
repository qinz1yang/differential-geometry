# `PairSmoothness.lean`

## Result

`MetricFamilySmoothOn.metricCLMSmoothAt` exposes joint smoothness of the
fully bundled metric bilinear continuous-linear map at a regular spacetime
point. It is reconstructed from native smooth frame components and is then
evaluated on moving tangent vectors by the standard bundle-CLM application
API.

## Verification and use

Focused verification and the targeted export refresh passed. The result is
used by L-speed and moving-pairing regularity; no Ricci-flow-specific
hypothesis was added to this generic metric-family layer.
