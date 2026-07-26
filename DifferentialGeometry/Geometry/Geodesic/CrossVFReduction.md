# CrossVFReduction status

## 2026-07-18

- `geodesicVF_smooth` is implemented and focused/exact GREEN.
- The proof is local and canonical: near each `p : TM`, the basepoint-free
  spray agrees with the chart-fixed spray based at `p.proj`; the existing
  fixed-chart smoothness theorem then transfers by eventual equality.
- No completeness, injectivity-radius, compactness, or new H6 hypothesis was
  added.
- The canonical module artifact has been refreshed successfully.

## Boundary

This closes global smoothness of the geodesic spray as a section of `T(TM)`.
It does **not** yet prove smooth dependence of its time-one flow on every
initial vector in the natural exponential domain.  The remaining H6 route is
to obtain local smooth flow charts from the global spray, continue them over a
finite time interval by uniqueness, and identify the resulting trajectory with
the intrinsic geodesic velocity lift.

## Progress

- `geodesicVF_smooth`: 100% after focused and exact verification.
- Finite-time smooth-flow continuation producer: theorem not yet stated, 0%;
  its global-spray prerequisite is now complete.
- Native `NormalRadiusProfile.le_exp_radius`: 0%; the dedicated zero-order
  radial/metric-equivalence machinery remains about 96% complete.
- Whole HCG compactness machinery remains about 60%; the unconditional
  textbook compactness endpoint remains 0%.

## Next target

Reuse `local_flow_chartIsLocalFlow_and_realisation` for the autonomous global
spray, then expose the smallest finite-time continuation/identification lemma
needed to make intrinsic exponential smooth on a compact injective ball.
